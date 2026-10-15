import SP1Clean.Extracted.SystemOracle.SyscallInstrs
import SP1Clean.Faithful.ChipOracle
import SP1Clean.Faithful.U16CompareOperation
import SP1Clean.Faithful.IsZeroOperation
import SP1Clean.Faithful.CPUState
import SP1Clean.Proofs.Chips.SyscallInstrsChip.Formal

/-! # Chip-level faithfulness anchor — SP1's whole `SyscallInstrs` table

The whole-table Rust oracle boundary for SP1's ECALL row: the native `SyscallInstrsChip` circuit's
complete `assertZero` list and complete interaction multiset, compared against
`Extracted/SystemOracle/SyscallInstrs.lean` — the extracted `sp1-constraint-compiler` dump of
upstream's `SyscallInstrsChip::eval` (`../sp1 crates/core/machine/src/syscall/instructions`).

## Shape of the anchor

Like `StateBump` and `MemoryBump`, this table has `localLength = 0`: all sixty-five cells are
inputs and the physical Clean row *is* the extracted flat `values` vector, so the anchor is stated
over the input-keyed codec rather than through the output-keyed `ChipRowCodec`. Unlike those two it
is not flat *internally* — the row composes fourteen subcircuits (the byte split, five `IsZero`
selectors, two `U16Compare` bounds, the `CPUState` reader, three `RegisterAccessCols` readers, and
the five arms of `Native/Chips/SyscallInstrsChip/Arms.lean`) — but `nativeAssertZeros` flattens
those, so the comparison is still between two flat lists.

## The public-value factoring (the one structural difference from the other anchors)

This is the first anchor whose Rust side reads `publicValues`. SP1 states eight of its conjuncts
against public values directly — the two commit flags at `[145]`/`[147]`, the four selected
committed-digest bytes out of `[32..63]`, the selected deferred byte out of `[72..79]`, and the
halt exit code at `[87]`. Clean's flat AIR localises the public input to the verifier row
(`Table` has no `PublicIO`, and `Ensemble.tables` cannot depend on the witness's public input), so
a chip-level public-value assertion **must** be a channel hand-off; the native row emits each as
one message built from columns it already carries.

`syscallInstrsChipConstraintsFaithful` is therefore an iff between the extracted assertion list and
*the native constraint system conjoined with* `PublicValueBinding` — those eight Rust conjuncts,
stated verbatim over the Rust row and its public values, so an auditor reads SP1's own expressions
rather than a paraphrase. The eight messages that carry them are pinned by
`syscallInstrsUnexpectedInteractions`. What is *not* yet proved is that each conjunct follows from
its message's payload: that needs a provider for `Channels.publicValuesChannel` and
`Channels.exitChannel`, which the ensemble does not have, and it is disclosed as the native-only-bus
row in `docs/assurance.md`.

## What this file proves

`syscallInstrsChip_faithful`: the two `ChipFaithful` clauses at the input-keyed row codec this table
needs. The extracted whole-table assertion system is equivalent to the native circuit's complete
constraint system on the reconstructed row together with `PublicValueBinding`, and the two complete
interaction multisets agree once the row's native-only public-value hand-off is added to the oracle
side.

Underneath: the sixty-five-cell codec and both round-trips; both complete lists decomposed into
their sixteen composed blocks and pinned block by block; five per-bus comparisons against the
oracle; and the constructive boundary. The assertion half is a checked bijection over eighty-one
propositions — the six copies of the `is_real` gate SP1's dump emits are matched by six distinct
native sources, not collapsed.

Two proof-engineering facts are worth carrying to the next anchor of this size, because both cost
real time here. Reducing a thirty-entry oracle list inside one `simp only` builds a monolithic
congruence term that the kernel cannot check; unfolding only the `@[irreducible]` oracle definitions
and letting `rfl` compute keeps the term small. And an `example` is checked far more cheaply than a
named theorem, so a probe that elaborates in seconds says nothing about the lemma it stands in for.

## The Memory and Program polarity bridges

As everywhere else: SP1 `.send`s the read-prior Memory record and the Program fetch where the
native circuit `pullIf`s them, and `nativeAccesses` (`Faithful/ChipOracle.lean`) applies
`LookupAccessList.negMult` to both blocks for exactly that reason. Byte and State are already
aligned.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel exitChannel
  syscallChannel publicValuesChannel MemoryMsg ProgramMsg)
open scoped SP1Clean.ConstraintCoe
open SP1Clean.SyscallInstrsChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]



/-! ## The whole-row column codec

The sixty-five-cell regrouping between the native `Inputs` row and the extracted flat vector. The
grouping is documented cell-by-cell in `FormalModel/Contracts/SyscallInstrsChip.lean`; this pair of
maps is the machine-checked version of that table, and the two round-trips below are what make it a
regrouping rather than a claim. -/

/-- Whole-row reconfiguration: the native `SyscallInstrsChip.Inputs` row in upstream
`SyscallInstrsCols` field order. -/
def syscallInstrsReconfigure {F : Type} (r : SyscallInstrsChip.Inputs F) :
    Extracted.SyscallInstrsCols F :=
  ⟨#v[
      r.state.clk_high, r.state.clk_16_24, r.state.clk_0_16, r.state.pc[0], r.state.pc[1],
      r.state.pc[2], r.op_a, r.op_a_memory.prev_value[0], r.op_a_memory.prev_value[1],
      r.op_a_memory.prev_value[2], r.op_a_memory.prev_value[3],
      r.op_a_memory.access_timestamp.prev_low, r.op_a_memory.access_timestamp.diff_low_limb,
      r.op_a_0, r.op_b, r.op_b_memory.prev_value[0], r.op_b_memory.prev_value[1],
      r.op_b_memory.prev_value[2], r.op_b_memory.prev_value[3],
      r.op_b_memory.access_timestamp.prev_low, r.op_b_memory.access_timestamp.diff_low_limb,
      r.op_c, r.op_c_memory.prev_value[0], r.op_c_memory.prev_value[1],
      r.op_c_memory.prev_value[2], r.op_c_memory.prev_value[3],
      r.op_c_memory.access_timestamp.prev_low, r.op_c_memory.access_timestamp.diff_low_limb,
      r.next_pc[0], r.next_pc[1], r.next_pc[2], r.is_halt, r.op_a_value[0], r.op_a_value[1],
      r.op_a_value[2], r.op_a_value[3], r.syscall_id_bytes.low_bytes[0],
      r.syscall_id_bytes.low_bytes[1], r.syscall_id_bytes.low_bytes[2],
      r.syscall_id_bytes.low_bytes[3], r.is_enter_unconstrained.inverse,
      r.is_enter_unconstrained.result, r.is_hint_len.inverse, r.is_hint_len.result,
      r.is_halt_zero.inverse, r.is_halt_zero.result, r.is_commit.inverse, r.is_commit.result,
      r.is_commit_deferred.inverse, r.is_commit_deferred.result, r.digest_index_bits[0],
      r.digest_index_bits[1], r.digest_index_bits[2], r.digest_index_bits[3],
      r.digest_index_bits[4], r.digest_index_bits[5], r.digest_index_bits[6],
      r.digest_index_bits[7], r.digest_word[0], r.digest_word[1], r.digest_word[2],
      r.digest_word[3], r.op_b_cmp.bit, r.op_c_cmp.bit, r.is_real]⟩

/-- Inverse whole-row map, used to reconstruct the native proof row from an arbitrary Rust row. -/
def syscallInstrsDeconfigure {F : Type} (cols : Extracted.SyscallInstrsCols F) :
    SyscallInstrsChip.Inputs F :=
  { state :=
      { clk_high := cols.values[0], clk_16_24 := cols.values[1], clk_0_16 := cols.values[2]
        pc := #v[cols.values[3], cols.values[4], cols.values[5]] }
    op_a := cols.values[6]
    op_a_memory :=
      { prev_value := #v[cols.values[7], cols.values[8], cols.values[9], cols.values[10]]
        access_timestamp := { prev_low := cols.values[11], diff_low_limb := cols.values[12] } }
    op_a_0 := cols.values[13]
    op_b := cols.values[14]
    op_b_memory :=
      { prev_value := #v[cols.values[15], cols.values[16], cols.values[17], cols.values[18]]
        access_timestamp := { prev_low := cols.values[19], diff_low_limb := cols.values[20] } }
    op_c := cols.values[21]
    op_c_memory :=
      { prev_value := #v[cols.values[22], cols.values[23], cols.values[24], cols.values[25]]
        access_timestamp := { prev_low := cols.values[26], diff_low_limb := cols.values[27] } }
    next_pc := #v[cols.values[28], cols.values[29], cols.values[30]]
    is_halt := cols.values[31]
    op_a_value := #v[cols.values[32], cols.values[33], cols.values[34], cols.values[35]]
    syscall_id_bytes :=
      { low_bytes := #v[cols.values[36], cols.values[37], cols.values[38], cols.values[39]] }
    is_enter_unconstrained := { inverse := cols.values[40], result := cols.values[41] }
    is_hint_len := { inverse := cols.values[42], result := cols.values[43] }
    is_halt_zero := { inverse := cols.values[44], result := cols.values[45] }
    is_commit := { inverse := cols.values[46], result := cols.values[47] }
    is_commit_deferred := { inverse := cols.values[48], result := cols.values[49] }
    digest_index_bits :=
      #v[cols.values[50], cols.values[51], cols.values[52], cols.values[53], cols.values[54],
         cols.values[55], cols.values[56], cols.values[57]]
    digest_word := #v[cols.values[58], cols.values[59], cols.values[60], cols.values[61]]
    op_b_cmp := { bit := cols.values[62] }
    op_c_cmp := { bit := cols.values[63] }
    is_real := cols.values[64] }

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- Vector eta at the four widths the row carries. -/
private theorem syscallVec_eta {F : Type} :
    (∀ w : Vector F 3, #v[w[0], w[1], w[2]] = w) ∧
      (∀ w : Vector F 4, #v[w[0], w[1], w[2], w[3]] = w) ∧
      (∀ w : Vector F 8, #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]] = w) :=
  ⟨fun w => by ext i hi; interval_cases i <;> rfl,
   fun w => by ext i hi; interval_cases i <;> rfl,
   fun w => by ext i hi; interval_cases i <;> rfl⟩

theorem syscallInstrsDeconfigure_reconfigure {F : Type} :
    Function.LeftInverse (syscallInstrsDeconfigure (F := F)) syscallInstrsReconfigure := by
  intro r
  obtain ⟨⟨-, -, -, -⟩, -, ⟨-, -⟩, -, -, ⟨-, -⟩, -, ⟨-, -⟩, -, -, -, -, -, -, -, -, -, -, -, -,
    -⟩ := r
  obtain ⟨h3, h4, h8⟩ := syscallVec_eta (F := F)
  simp [syscallInstrsReconfigure, syscallInstrsDeconfigure, h3, h4, h8]

theorem syscallInstrsReconfigure_deconfigure {F : Type} :
    Function.LeftInverse (syscallInstrsReconfigure (F := F)) syscallInstrsDeconfigure := by
  intro cols
  obtain ⟨values⟩ := cols
  simp only [syscallInstrsDeconfigure, syscallInstrsReconfigure,
    Extracted.SyscallInstrsCols.mk.injEq]
  ext i hi
  interval_cases i <;> rfl

/-- SP1 Rust's complete `SyscallInstrs` oracle, viewed from the native Lean row. Unlike every other
chip oracle in this directory the public values are genuinely *read* by `asserts`, so they are not
merely carried along; see the module docstring for how the anchor factors them. -/
def syscallInstrsChipOracle (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) :
    ChipOracle (ZMod p) SyscallInstrsChip.Inputs Extracted.SyscallInstrsCols where
  reconfigure := syscallInstrsReconfigure
  deconfigure := syscallInstrsDeconfigure
  reconfigure_deconfigure := syscallInstrsReconfigure_deconfigure
  deconfigure_reconfigure := syscallInstrsDeconfigure_reconfigure
  assertZeros cols := Extracted.SyscallInstrsCols.asserts cols preprocessed publicValues
  interactions cols := Extracted.SyscallInstrsCols.interactions cols preprocessed publicValues

/-! ## The physical row -/

/-- The physical Clean row: the typed input followed by an empty witness block. -/
def syscallInstrsPhysicalRow {F : Type} (r : SyscallInstrsChip.Inputs F) : Array F :=
  inputFirstRow r #v[]

/-- The verifier environment a Rust row induces on the native chip. -/
def syscallInstrsEnvironment (cols : Extracted.SyscallInstrsCols (ZMod p))
    (data : ProverData (ZMod p)) : Environment (ZMod p) :=
  Environment.fromArray (syscallInstrsPhysicalRow (syscallInstrsDeconfigure cols)) data

/-- The table's physical width: sixty-five input cells and no witness block. -/
theorem syscallInstrsChip_size_eq :
    (SyscallInstrsChip.circuit (p := p)).size = size SyscallInstrsChip.Inputs := by
  rw [GeneralFormalCircuit.size_eq, SyscallInstrsChip.circuit_localLength, Nat.add_zero]

/-- The reconstructed row has exactly the flat component's width. -/
theorem syscallInstrsPhysicalRow_size (cols : Extracted.SyscallInstrsCols (ZMod p)) :
    (syscallInstrsPhysicalRow (syscallInstrsDeconfigure cols)).size =
      ({ circuit := SyscallInstrsChip.circuit (p := p) } : Air.Flat.Component (ZMod p)).width := by
  rw [syscallInstrsPhysicalRow, inputFirstRow_size, Air.Flat.Component.width,
    syscallInstrsChip_size_eq]
  simp

/-- The reconstructed row decodes back to the native row the codec started from. -/
theorem syscallInstrsEnvironment_rowInput (cols : Extracted.SyscallInstrsCols (ZMod p))
    (data : ProverData (ZMod p)) :
    ({ circuit := SyscallInstrsChip.circuit (p := p) } : Air.Flat.Component (ZMod p)).rowInput
        (syscallInstrsEnvironment cols data) = syscallInstrsDeconfigure cols :=
  rowInput_inputFirstRow _ _ _ _

omit [Fact (2 ^ 17 < p)] in
/-- The component's row input *variables* evaluate to the decoded native row. -/
theorem syscallInstrsEnvironment_eval (cols : Extracted.SyscallInstrsCols (ZMod p))
    (data : ProverData (ZMod p)) :
    Eval.eval (syscallInstrsEnvironment cols data)
        (varFromOffset SyscallInstrsChip.Inputs 0 : Var SyscallInstrsChip.Inputs (ZMod p)) =
      syscallInstrsDeconfigure cols :=
  eval_inputFirstRow _ _ _

/-! ## Component-wise evaluation

`Eval.eval` on a `ProvableStruct` is field-wise; these five lemmas say so at each carrier the row
uses, and are what turn one whole-row binding into sixty-five cell equations. -/

theorem eval_syscallCPUState {F : Type} [FiniteField F]
    (env : Environment F) (c : Circuits.Types.CPUState (Expression F)) :
    Eval.eval env c =
      ({ clk_high := Eval.eval env c.clk_high
         clk_16_24 := Eval.eval env c.clk_16_24
         clk_0_16 := Eval.eval env c.clk_0_16
         pc := Eval.eval env c.pc } : Circuits.Types.CPUState F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_syscallTimestamp {F : Type} [FiniteField F]
    (env : Environment F) (t : Circuits.Types.RegisterAccessTimestamp (Expression F)) :
    Eval.eval env t =
      ({ prev_low := Eval.eval env t.prev_low
         diff_low_limb := Eval.eval env t.diff_low_limb } :
        Circuits.Types.RegisterAccessTimestamp F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_syscallAccess {F : Type} [FiniteField F]
    (env : Environment F) (a : Circuits.Types.RegisterAccessCols (Expression F)) :
    Eval.eval env a =
      ({ prev_value := Eval.eval env a.prev_value
         access_timestamp := Eval.eval env a.access_timestamp } :
        Circuits.Types.RegisterAccessCols F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_syscallIsZero {F : Type} [FiniteField F]
    (env : Environment F) (z : Circuits.Types.IsZeroOperation (Expression F)) :
    Eval.eval env z =
      ({ inverse := Eval.eval env z.inverse
         result := Eval.eval env z.result } : Circuits.Types.IsZeroOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_syscallU16toU8 {F : Type} [FiniteField F]
    (env : Environment F) (u : Circuits.Types.U16toU8Operation (Expression F)) :
    Eval.eval env u =
      ({ low_bytes := Eval.eval env u.low_bytes } : Circuits.Types.U16toU8Operation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_syscallU16Compare {F : Type} [FiniteField F]
    (env : Environment F) (c : Circuits.Types.U16CompareOperation (Expression F)) :
    Eval.eval env c =
      ({ bit := Eval.eval env c.bit } : Circuits.Types.U16CompareOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

theorem eval_syscallInstrsInputs {F : Type} [FiniteField F]
    (env : Environment F) (r : SyscallInstrsChip.Inputs (Expression F)) :
    Eval.eval env r =
      ({ state := Eval.eval env r.state
         op_a := Eval.eval env r.op_a
         op_a_memory := Eval.eval env r.op_a_memory
         op_a_0 := Eval.eval env r.op_a_0
         op_b := Eval.eval env r.op_b
         op_b_memory := Eval.eval env r.op_b_memory
         op_c := Eval.eval env r.op_c
         op_c_memory := Eval.eval env r.op_c_memory
         next_pc := Eval.eval env r.next_pc
         is_halt := Eval.eval env r.is_halt
         op_a_value := Eval.eval env r.op_a_value
         syscall_id_bytes := Eval.eval env r.syscall_id_bytes
         is_enter_unconstrained := Eval.eval env r.is_enter_unconstrained
         is_hint_len := Eval.eval env r.is_hint_len
         is_halt_zero := Eval.eval env r.is_halt_zero
         is_commit := Eval.eval env r.is_commit
         is_commit_deferred := Eval.eval env r.is_commit_deferred
         digest_index_bits := Eval.eval env r.digest_index_bits
         digest_word := Eval.eval env r.digest_word
         op_b_cmp := Eval.eval env r.op_b_cmp
         op_c_cmp := Eval.eval env r.op_c_cmp
         is_real := Eval.eval env r.is_real } : SyscallInstrsChip.Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

/-! ## The evaluated Rust row

Every downstream statement is phrased over `syscallInstrsRustColumns`: the extracted flat vector
whose cells are literally the native row's evaluated columns. One theorem — sixty-five uniform
cases — connects it to the codec, and after that the Rust oracle's `cols.values[k]` accesses reduce
definitionally to native expressions, so no further column bookkeeping is needed. -/

/-- The extracted Rust row a native row induces under an environment. -/
def syscallInstrsRustColumns (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) : Extracted.SyscallInstrsCols (ZMod p) :=
  ⟨#v[
      Expression.eval env r.state.clk_high, Expression.eval env r.state.clk_16_24,
      Expression.eval env r.state.clk_0_16, Expression.eval env r.state.pc[0],
      Expression.eval env r.state.pc[1], Expression.eval env r.state.pc[2],
      Expression.eval env r.op_a, Expression.eval env r.op_a_memory.prev_value[0],
      Expression.eval env r.op_a_memory.prev_value[1],
      Expression.eval env r.op_a_memory.prev_value[2],
      Expression.eval env r.op_a_memory.prev_value[3],
      Expression.eval env r.op_a_memory.access_timestamp.prev_low,
      Expression.eval env r.op_a_memory.access_timestamp.diff_low_limb,
      Expression.eval env r.op_a_0, Expression.eval env r.op_b,
      Expression.eval env r.op_b_memory.prev_value[0],
      Expression.eval env r.op_b_memory.prev_value[1],
      Expression.eval env r.op_b_memory.prev_value[2],
      Expression.eval env r.op_b_memory.prev_value[3],
      Expression.eval env r.op_b_memory.access_timestamp.prev_low,
      Expression.eval env r.op_b_memory.access_timestamp.diff_low_limb,
      Expression.eval env r.op_c, Expression.eval env r.op_c_memory.prev_value[0],
      Expression.eval env r.op_c_memory.prev_value[1],
      Expression.eval env r.op_c_memory.prev_value[2],
      Expression.eval env r.op_c_memory.prev_value[3],
      Expression.eval env r.op_c_memory.access_timestamp.prev_low,
      Expression.eval env r.op_c_memory.access_timestamp.diff_low_limb,
      Expression.eval env r.next_pc[0], Expression.eval env r.next_pc[1],
      Expression.eval env r.next_pc[2], Expression.eval env r.is_halt,
      Expression.eval env r.op_a_value[0], Expression.eval env r.op_a_value[1],
      Expression.eval env r.op_a_value[2], Expression.eval env r.op_a_value[3],
      Expression.eval env r.syscall_id_bytes.low_bytes[0],
      Expression.eval env r.syscall_id_bytes.low_bytes[1],
      Expression.eval env r.syscall_id_bytes.low_bytes[2],
      Expression.eval env r.syscall_id_bytes.low_bytes[3],
      Expression.eval env r.is_enter_unconstrained.inverse,
      Expression.eval env r.is_enter_unconstrained.result,
      Expression.eval env r.is_hint_len.inverse, Expression.eval env r.is_hint_len.result,
      Expression.eval env r.is_halt_zero.inverse, Expression.eval env r.is_halt_zero.result,
      Expression.eval env r.is_commit.inverse, Expression.eval env r.is_commit.result,
      Expression.eval env r.is_commit_deferred.inverse,
      Expression.eval env r.is_commit_deferred.result,
      Expression.eval env r.digest_index_bits[0], Expression.eval env r.digest_index_bits[1],
      Expression.eval env r.digest_index_bits[2], Expression.eval env r.digest_index_bits[3],
      Expression.eval env r.digest_index_bits[4], Expression.eval env r.digest_index_bits[5],
      Expression.eval env r.digest_index_bits[6], Expression.eval env r.digest_index_bits[7],
      Expression.eval env r.digest_word[0], Expression.eval env r.digest_word[1],
      Expression.eval env r.digest_word[2], Expression.eval env r.digest_word[3],
      Expression.eval env r.op_b_cmp.bit, Expression.eval env r.op_c_cmp.bit,
      Expression.eval env r.is_real]⟩

omit [Fact (2 ^ 17 < p)] in
/-- Reconfiguring an evaluated native row is evaluating it cell by cell. -/
theorem syscallInstrsReconfigure_eval (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) :
    syscallInstrsReconfigure (Eval.eval env r) = syscallInstrsRustColumns env r := by
  rw [eval_syscallInstrsInputs]
  simp only [syscallInstrsReconfigure, syscallInstrsRustColumns,
    eval_syscallCPUState, eval_syscallAccess, eval_syscallTimestamp, eval_syscallU16toU8,
    eval_syscallIsZero, eval_syscallU16Compare, ProvableType.eval_field,
    Extracted.SyscallInstrsCols.mk.injEq]
  ext i hi
  interval_cases i <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero, ProvableType.getElem_eval_fields]

/-! ## The native assertion system, block by block

`circuit_norm` cannot be used here: it normalises the *content* of seventy-odd constraints to
answer a question about their *arrangement*, and exceeds the elaboration budget on a row this wide.
The structural `Operations.constraints_*` lemmas answer it directly. Every subcircuit sits at the
same offset because the row witnesses nothing — `localLength = 0` throughout. -/

/-- The row's complete evaluated `assertZero` list, split into its thirteen shallow gates and the
sixteen composed blocks, each left folded at its own `main`. -/
theorem syscallInstrsAssertBlocks (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((SyscallInstrsChip.main r).operations offset) =
      [Expression.eval env (r.is_real * (r.is_real - 1)),
       Expression.eval env (r.is_commit.result * (r.is_commit.result - 1)),
       Expression.eval env (r.is_commit_deferred.result * (r.is_commit_deferred.result - 1)),
       Expression.eval env (r.is_halt * (r.is_halt - 1)),
       Expression.eval env (tableByteVar r * (tableByteVar r - 1))] ++
      nativeAssertZeros env
        ((SP1Clean.U16toU8OperationSafe.circuit.main ⟨r.op_a_memory.prev_value, r.syscall_id_bytes, r.is_real⟩).operations offset) ++
      nativeAssertZeros env
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst haltCode, r.is_halt_zero, r.is_real⟩).operations offset) ++
      nativeAssertZeros env
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst enterUnconstrainedCode, r.is_enter_unconstrained, r.is_real⟩).operations offset) ++
      nativeAssertZeros env
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst hintLenCode, r.is_hint_len, r.is_real⟩).operations offset) ++
      nativeAssertZeros env
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst commitCode, r.is_commit, r.is_real⟩).operations offset) ++
      nativeAssertZeros env
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst commitDeferredCode, r.is_commit_deferred, r.is_real⟩).operations offset) ++
      [Expression.eval env (r.is_halt - r.is_halt_zero.result * r.is_real),
       Expression.eval env ((r.is_real - 1) * tableByteVar r),
       Expression.eval env ((r.is_real - 1) * r.is_halt),
       Expression.eval env ((r.is_real - 1) * r.is_commit_deferred.result)] ++
      nativeAssertZeros env
        ((Readers.CPUState.circuit.main ⟨r.state, r.next_pc, 264, r.is_real⟩).operations offset) ++
      nativeAssertZeros env
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_a_memory, r.is_real, clkLowVar r + 4⟩).operations offset) ++
      nativeAssertZeros env
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_b_memory, r.is_real, clkLowVar r + 3⟩).operations offset) ++
      nativeAssertZeros env
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_c_memory, r.is_real, clkLowVar r + 2⟩).operations offset) ++
      nativeAssertZeros env
        ((SyscallInstrsChip.WriteArm.circuit.main
          ⟨r.op_a_memory.prev_value, r.op_a_value, r.op_a_0,
           r.is_enter_unconstrained.result, r.is_hint_len.result, r.is_real⟩).operations offset) ++
      nativeAssertZeros env
        ((SyscallInstrsChip.PcArm.circuit.main ⟨r.state.pc, r.next_pc, r.is_real, r.is_halt⟩).operations offset) ++
      nativeAssertZeros env
        ((SyscallInstrsChip.DispatchArm.circuit.main ⟨r.op_b_memory.prev_value, r.op_c_memory.prev_value, tableByteVar r⟩).operations offset) ++
      nativeAssertZeros env
        ((SyscallInstrsChip.FieldBoundArm.circuit.main ⟨r.op_b_memory.prev_value, r.op_b_cmp.bit, r.is_halt⟩).operations offset) ++
      nativeAssertZeros env
        ((SyscallInstrsChip.FieldBoundArm.circuit.main
          ⟨r.op_c_memory.prev_value, r.op_c_cmp.bit, r.is_commit_deferred.result⟩).operations offset) ++
      nativeAssertZeros env
        ((SyscallInstrsChip.CommitArm.circuit.main
          ⟨r.digest_index_bits, r.digest_word, r.op_b_memory.prev_value,
           r.op_c_memory.prev_value, r.is_commit.result, r.is_commit_deferred.result, r.is_real⟩).operations offset) := by
  simp only [nativeAssertZeros, SyscallInstrsChip.main, Circuit.operations, Circuit.bind_def,
    assertZero, subcircuitWithAssertion, assertion, Channel.pullIf, Channel.pushIf,
    Operations.constraints_assert, Operations.constraints_interact,
    Operations.constraints_nil, Operations.constraints_subcircuit,
    FormalAssertion.toSubcircuit_constraints, GeneralFormalCircuit.toSubcircuit_constraints,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    Readers.CPUState.circuit_localLength, Readers.RegisterAccessCols.circuit_localLength,
    SP1Clean.IsZeroOperation.circuit_localLength,
    SyscallInstrsChip.PcArm.circuit_localLength,
    SyscallInstrsChip.WriteArm.circuit_localLength,
    SyscallInstrsChip.FieldBoundArm.circuit_localLength,
    SyscallInstrsChip.DispatchArm.circuit_localLength,
    SP1Clean.U16toU8OperationSafe.circuit_localLength,
    Operations.localLength, Nat.add_zero,
    List.map_append, List.map_cons, List.nil_append, List.append_nil,
    List.append_assoc, List.cons_append]

/-! ## Each composed block's assertion list

One lemma per composed circuit, each proved over an **opaque** input of that circuit's own row type.
That is what keeps `circuit_norm` affordable: applied to the whole sixty-five-column row at once it
exceeds the budget, applied to one arm at a time it is instant. Three of the blocks — the byte
split and the two reader families — assert only their own `is_real` gate; together with the chip's
own gate they are the six copies SP1's dump repeats. -/

omit [Fact (2 ^ 17 < p)] in
theorem pcArmAssertions (env : Environment (ZMod p))
    (input : Var SyscallInstrsChip.PcArm.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((SyscallInstrsChip.PcArm.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).is_real *
        ((1 - (ProvableStruct.eval env input).is_halt) * ((ProvableStruct.eval env input).next_pc[0] - ((ProvableStruct.eval env input).pc[0] + 4))),
       (ProvableStruct.eval env input).is_real *
        ((1 - (ProvableStruct.eval env input).is_halt) * ((ProvableStruct.eval env input).next_pc[1] - (ProvableStruct.eval env input).pc[1])),
       (ProvableStruct.eval env input).is_real *
        ((1 - (ProvableStruct.eval env input).is_halt) * ((ProvableStruct.eval env input).next_pc[2] - (ProvableStruct.eval env input).pc[2])),
       (ProvableStruct.eval env input).is_halt * ((ProvableStruct.eval env input).next_pc[0] - 1),
       (ProvableStruct.eval env input).is_halt * (ProvableStruct.eval env input).next_pc[1],
       (ProvableStruct.eval env input).is_halt * (ProvableStruct.eval env input).next_pc[2]] := by
  simp only [nativeAssertZeros, SyscallInstrsChip.PcArm.circuit, SyscallInstrsChip.PcArm.main,
    circuit_norm]

omit [Fact (2 ^ 17 < p)] in
theorem dispatchArmAssertions (env : Environment (ZMod p))
    (input : Var SyscallInstrsChip.DispatchArm.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((SyscallInstrsChip.DispatchArm.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).table_byte * (ProvableStruct.eval env input).op_b[3], (ProvableStruct.eval env input).table_byte * (ProvableStruct.eval env input).op_c[3]] := by
  simp only [nativeAssertZeros, SyscallInstrsChip.DispatchArm.circuit,
    SyscallInstrsChip.DispatchArm.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
theorem writeArmAssertions (env : Environment (ZMod p))
    (input : Var SyscallInstrsChip.WriteArm.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((SyscallInstrsChip.WriteArm.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).is_real * (ProvableStruct.eval env input).op_a_0,
       (ProvableStruct.eval env input).op_a_0 * (ProvableStruct.eval env input).op_a_value[0],
       (ProvableStruct.eval env input).op_a_0 * (ProvableStruct.eval env input).op_a_value[1],
       (ProvableStruct.eval env input).op_a_0 * (ProvableStruct.eval env input).op_a_value[2],
       (ProvableStruct.eval env input).op_a_0 * (ProvableStruct.eval env input).op_a_value[3],
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).is_enter_unconstrained * (ProvableStruct.eval env input).op_a_value[0]),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).is_enter_unconstrained * (ProvableStruct.eval env input).op_a_value[1]),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).is_enter_unconstrained * (ProvableStruct.eval env input).op_a_value[2]),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).is_enter_unconstrained * (ProvableStruct.eval env input).op_a_value[3]),
       (ProvableStruct.eval env input).is_real *
        (((ProvableStruct.eval env input).is_enter_unconstrained + (ProvableStruct.eval env input).is_hint_len - 1) *
          ((ProvableStruct.eval env input).op_a_value[0] - (ProvableStruct.eval env input).op_a_prev[0])),
       (ProvableStruct.eval env input).is_real *
        (((ProvableStruct.eval env input).is_enter_unconstrained + (ProvableStruct.eval env input).is_hint_len - 1) *
          ((ProvableStruct.eval env input).op_a_value[1] - (ProvableStruct.eval env input).op_a_prev[1])),
       (ProvableStruct.eval env input).is_real *
        (((ProvableStruct.eval env input).is_enter_unconstrained + (ProvableStruct.eval env input).is_hint_len - 1) *
          ((ProvableStruct.eval env input).op_a_value[2] - (ProvableStruct.eval env input).op_a_prev[2])),
       (ProvableStruct.eval env input).is_real *
        (((ProvableStruct.eval env input).is_enter_unconstrained + (ProvableStruct.eval env input).is_hint_len - 1) *
          ((ProvableStruct.eval env input).op_a_value[3] - (ProvableStruct.eval env input).op_a_prev[3]))] := by
  simp only [nativeAssertZeros, SyscallInstrsChip.WriteArm.circuit,
    SyscallInstrsChip.WriteArm.main, circuit_norm]

omit [Fact (2 ^ 17 < p)] in
theorem commitArmAssertions (env : Environment (ZMod p))
    (input : Var SyscallInstrsChip.CommitArm.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((SyscallInstrsChip.CommitArm.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[0] * ((ProvableStruct.eval env input).index_bits[0] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[1] * ((ProvableStruct.eval env input).index_bits[1] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[2] * ((ProvableStruct.eval env input).index_bits[2] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[3] * ((ProvableStruct.eval env input).index_bits[3] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[4] * ((ProvableStruct.eval env input).index_bits[4] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[5] * ((ProvableStruct.eval env input).index_bits[5] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[6] * ((ProvableStruct.eval env input).index_bits[6] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[7] * ((ProvableStruct.eval env input).index_bits[7] - 1)),
       (ProvableStruct.eval env input).is_real *
        (((ProvableStruct.eval env input).is_commit + (ProvableStruct.eval env input).is_commit_deferred) * ((ProvableStruct.eval env input).index_bits[0] + (ProvableStruct.eval env input).index_bits[1] + (ProvableStruct.eval env input).index_bits[2] + (ProvableStruct.eval env input).index_bits[3] + (ProvableStruct.eval env input).index_bits[4] + (ProvableStruct.eval env input).index_bits[5] + (ProvableStruct.eval env input).index_bits[6] + (ProvableStruct.eval env input).index_bits[7] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((1 - ((ProvableStruct.eval env input).is_commit + (ProvableStruct.eval env input).is_commit_deferred)) * ((ProvableStruct.eval env input).index_bits[0] + (ProvableStruct.eval env input).index_bits[1] + (ProvableStruct.eval env input).index_bits[2] + (ProvableStruct.eval env input).index_bits[3] + (ProvableStruct.eval env input).index_bits[4] + (ProvableStruct.eval env input).index_bits[5] + (ProvableStruct.eval env input).index_bits[6] + (ProvableStruct.eval env input).index_bits[7])),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[0] * ((ProvableStruct.eval env input).op_b[0] - 0)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[1] * ((ProvableStruct.eval env input).op_b[0] - 1)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[2] * ((ProvableStruct.eval env input).op_b[0] - 2)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[3] * ((ProvableStruct.eval env input).op_b[0] - 3)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[4] * ((ProvableStruct.eval env input).op_b[0] - 4)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[5] * ((ProvableStruct.eval env input).op_b[0] - 5)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[6] * ((ProvableStruct.eval env input).op_b[0] - 6)),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).index_bits[7] * ((ProvableStruct.eval env input).op_b[0] - 7)),
       (ProvableStruct.eval env input).is_real *
        (((ProvableStruct.eval env input).is_commit + (ProvableStruct.eval env input).is_commit_deferred) *
          ((ProvableStruct.eval env input).op_b[1] + (ProvableStruct.eval env input).op_b[2] + (ProvableStruct.eval env input).op_b[3])),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).is_commit *
          ((ProvableStruct.eval env input).digest_word[0] + (ProvableStruct.eval env input).digest_word[1] * 256 - (ProvableStruct.eval env input).op_c[0])),
       (ProvableStruct.eval env input).is_real *
        ((ProvableStruct.eval env input).is_commit *
          ((ProvableStruct.eval env input).digest_word[2] + (ProvableStruct.eval env input).digest_word[3] * 256 - (ProvableStruct.eval env input).op_c[1])),
       (ProvableStruct.eval env input).is_real * ((ProvableStruct.eval env input).is_commit * (ProvableStruct.eval env input).op_c[2]),
       (ProvableStruct.eval env input).is_real * ((ProvableStruct.eval env input).is_commit * (ProvableStruct.eval env input).op_c[3])] := by
  simp only [nativeAssertZeros, SyscallInstrsChip.CommitArm.circuit,
    SyscallInstrsChip.CommitArm.main, SyscallInstrsChip.CommitArm.bitSumVar, circuit_norm]

theorem fieldBoundArmAssertions (env : Environment (ZMod p))
    (input : Var SyscallInstrsChip.FieldBoundArm.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((SyscallInstrsChip.FieldBoundArm.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).is_real * (ProvableStruct.eval env input).word[2], (ProvableStruct.eval env input).is_real * (ProvableStruct.eval env input).word[3]] ++
      Extracted.U16CompareOperation.asserts (ProvableStruct.eval env input).word[1] ((fieldLimbBound : ℕ) : ZMod p)
        ⟨(ProvableStruct.eval env input).bit⟩ (ProvableStruct.eval env input).is_real ++
      [(ProvableStruct.eval env input).is_real *
        (((ProvableStruct.eval env input).bit - 1) * ((ProvableStruct.eval env input).word[1] - ((fieldLimbBound : ℕ) : ZMod p))),
       (ProvableStruct.eval env input).is_real * (((ProvableStruct.eval env input).bit - 1) * (ProvableStruct.eval env input).word[0])] := by
  have h : ∀ (i : Var SP1Clean.U16CompareOperation.Inputs (ZMod p)) (o : ℕ),
      List.map (Expression.eval env)
          (Operations.constraints ((SP1Clean.U16CompareOperation.circuit.main i) o).2) =
        Extracted.U16CompareOperation.asserts (Expression.eval env i.a) (Expression.eval env i.b)
          (Eval.eval env i.cols) (Expression.eval env i.is_real) :=
    fun i o => u16compare_assertions_exact env i o
  simp only [nativeAssertZeros, SyscallInstrsChip.FieldBoundArm.circuit,
    SyscallInstrsChip.FieldBoundArm.main, circuit_norm, List.map_append, h]

/-- SP1's byte split read back at element 0 and 1: the syscall identifier proper, and the
"this handler has its own table" flag. These are exactly the native row's `syscallIdVar` and
`tableByteVar`, which is what lets the two dispatch arms line up. -/
theorem u16toU8SafeValue_head {F : Type} [Field F] [CoeHead F ℕ] (u : Vector F 4)
    (c : Circuits.Types.U16toU8Operation F) (g : F) :
    (Extracted.U16toU8OperationSafe.value u c g)[0] = c.low_bytes[0] ∧
      (Extracted.U16toU8OperationSafe.value u c g)[1] =
        (u[0] - c.low_bytes[0]) * (256 : F)⁻¹ := by
  constructor <;> simp [Extracted.U16toU8OperationSafe.value]

omit [Fact (2 ^ 17 < p)] in
/-- `isZero_assertions_exact` at the bundled circuit's `main`. The two spellings are definitionally
equal, but simp matches syntactically and the row composes the bundle. -/
theorem isZeroCircuitAssertions (env : Environment (ZMod p))
    (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((SP1Clean.IsZeroOperation.circuit.main input).operations offset) =
      Extracted.IsZeroOperation.asserts (Expression.eval env input.a) (Eval.eval env input.cols)
        (Expression.eval env input.is_real) :=
  isZero_assertions_exact env input offset

theorem u16toU8SafeAssertions (env : Environment (ZMod p))
    (input : Var SP1Clean.U16toU8OperationSafe.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env
        ((SP1Clean.U16toU8OperationSafe.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).is_real * ((ProvableStruct.eval env input).is_real - 1)] := by
  simp only [nativeAssertZeros, SP1Clean.U16toU8OperationSafe.circuit,
    SP1Clean.U16toU8OperationSafe.main, circuit_norm]

theorem cpuStateAssertList (env : Environment (ZMod p))
    (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((Readers.CPUState.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).is_real * ((ProvableStruct.eval env input).is_real - 1)] := by
  simp only [nativeAssertZeros, Readers.CPUState.circuit, Readers.CPUState.main, circuit_norm]

theorem registerAccessColsAssertions (env : Environment (ZMod p))
    (input : Var Readers.RegisterAccessCols.Inputs (ZMod p)) (offset : ℕ) :
    nativeAssertZeros env ((Readers.RegisterAccessCols.circuit.main input).operations offset) =
      [(ProvableStruct.eval env input).is_real * ((ProvableStruct.eval env input).is_real - 1)] := by
  simp only [nativeAssertZeros, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main, Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, circuit_norm]

/-! ## The public-value binding

SP1 states eight of its conjuncts against `publicValues`. Clean's flat AIR has no chip-level access
to them (`Table` carries no `PublicIO`), so the native row emits each as a channel message instead
and this predicate is what the anchor carries in their place — stated verbatim over the Rust row
and its public values, so an auditor reads SP1's own expressions rather than a paraphrase.

`syscallInstrsPublicValueBinding_via_messages` below identifies each conjunct with the payload of a
specific emitted message, which is what makes this a factoring rather than an omission. -/

/-- SP1's one-hot selection of a committed-digest byte out of `publicValues[32..63]`: the bitmap
`cols.values[50..57]` picks one of the eight words, and `k` picks the byte within it. -/
def commitDigestByte (cols : Extracted.SyscallInstrsCols (ZMod p)) (pv : Vector (ZMod p) 160) :
    Vector (ZMod p) 4 :=
  #v[0 + pv[32] * cols.values[50] +
    pv[36] * cols.values[51] +
    pv[40] * cols.values[52] +
    pv[44] * cols.values[53] +
    pv[48] * cols.values[54] +
    pv[52] * cols.values[55] +
    pv[56] * cols.values[56] +
    pv[60] * cols.values[57],
     0 + pv[33] * cols.values[50] +
    pv[37] * cols.values[51] +
    pv[41] * cols.values[52] +
    pv[45] * cols.values[53] +
    pv[49] * cols.values[54] +
    pv[53] * cols.values[55] +
    pv[57] * cols.values[56] +
    pv[61] * cols.values[57],
     0 + pv[34] * cols.values[50] +
    pv[38] * cols.values[51] +
    pv[42] * cols.values[52] +
    pv[46] * cols.values[53] +
    pv[50] * cols.values[54] +
    pv[54] * cols.values[55] +
    pv[58] * cols.values[56] +
    pv[62] * cols.values[57],
     0 + pv[35] * cols.values[50] +
    pv[39] * cols.values[51] +
    pv[43] * cols.values[52] +
    pv[47] * cols.values[53] +
    pv[51] * cols.values[54] +
    pv[55] * cols.values[55] +
    pv[59] * cols.values[56] +
    pv[63] * cols.values[57]]

/-- The same selection over the deferred-proof digest block `publicValues[72..79]`, which stores one
byte per word rather than four. -/
def deferredDigestByte (cols : Extracted.SyscallInstrsCols (ZMod p)) (pv : Vector (ZMod p) 160) :
    ZMod p :=
  0 + pv[72] * cols.values[50] +
    pv[73] * cols.values[51] +
    pv[74] * cols.values[52] +
    pv[75] * cols.values[53] +
    pv[76] * cols.values[54] +
    pv[77] * cols.values[55] +
    pv[78] * cols.values[56] +
    pv[79] * cols.values[57]

/-- SP1's four-limb field reduction as the extracted dump writes it, with the coefficients
`1, 2 ^ 16, 2 ^ 32, 2 ^ 48` **already reduced at KoalaBear's modulus** — the two large literals are
not the generic powers, which is external report Finding 7. Confining them here keeps the native
half of the anchor field-generic. -/
def koalaReduce (cols : Extracted.SyscallInstrsCols (ZMod p)) (i₀ : ℕ) : ZMod p :=
  match i₀ with
  | 15 => 0 + 1 * cols.values[15] +
    65536 * cols.values[16] +
    33554430 * cols.values[17] +
    134085624 * cols.values[18]
  | _ => 0 + 1 * cols.values[22] +
    65536 * cols.values[23] +
    33554430 * cols.values[24] +
    134085624 * cols.values[25]

/-- The eight conjuncts of SP1's `SyscallInstrs` assertion system that read `publicValues`: the two
commit flags, the four selected committed-digest bytes, the selected deferred byte against `a1`, and
the halt exit code against `publicValues[87]`. -/
def PublicValueBinding (cols : Extracted.SyscallInstrsCols (ZMod p))
    (pv : Vector (ZMod p) 160) : Prop :=
  cols.values[47] * (pv[145] - 1) = 0 ∧
    cols.values[49] * (pv[147] - 1) = 0 ∧
    cols.values[47] * ((commitDigestByte cols pv)[0] - cols.values[58]) = 0 ∧
    cols.values[47] * ((commitDigestByte cols pv)[1] - cols.values[59]) = 0 ∧
    cols.values[47] * ((commitDigestByte cols pv)[2] - cols.values[60]) = 0 ∧
    cols.values[47] * ((commitDigestByte cols pv)[3] - cols.values[61]) = 0 ∧
    cols.values[64] * (cols.values[49] * (deferredDigestByte cols pv - koalaReduce cols 22)) = 0 ∧
    cols.values[31] * (koalaReduce cols 15 - pv[87]) = 0

/-! ## Assertion-system agreement -/

/-- **Chip-level faithfulness anchor — assertion half.** SP1's generated whole-table `SyscallInstrs`
assertion list holds exactly when the native circuit's complete `assertZero` list does **and** the
eight public-value conjuncts hold. The two sides are the same eighty-one propositions: seven
composed sub-operation blocks that match block for block, sixty-six scalars that match one for one
after `x - 0` and `0 - x` are normalised, and the eight of `PublicValueBinding`.

Only two conjuncts are not a direct match. SP1 compares the *selected public-value digest* against
`a1`, where the native row compares its *cached* `digest_word`; the two are interderivable from the
digest-byte bindings without dividing by the commit selector, which is what the two
`linear_combination` steps do. -/
theorem syscallInstrsChipConstraintsFaithful
    (preprocessed : Vector (ZMod p) 0) (publicValues : Vector (ZMod p) 160)
    (env : Environment (ZMod p)) (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Forall (· = 0)
        (Extracted.SyscallInstrsCols.asserts (syscallInstrsRustColumns env r) preprocessed
          publicValues) ↔
      (List.Forall (· = 0)
          (nativeAssertZeros env ((SyscallInstrsChip.main r).operations offset)) ∧
        PublicValueBinding (syscallInstrsRustColumns env r) publicValues) := by
  rw [syscallInstrsAssertBlocks]
  simp only [Extracted.SyscallInstrsCols.asserts, syscallInstrsRustColumns,
    Extracted.U16toU8OperationSafe.asserts, u16toU8SafeAssertions, cpuStateAssertList,
    registerAccessColsAssertions, pcArmAssertions, dispatchArmAssertions, writeArmAssertions,
    commitArmAssertions, fieldBoundArmAssertions, isZeroCircuitAssertions,
    PublicValueBinding, commitDigestByte, deferredDigestByte, koalaReduce,
    syscallIdVar, tableByteVar, natConst, haltCode, enterUnconstrainedCode, hintLenCode,
    commitCode, commitDeferredCode, fieldLimbBound,
    u16toU8SafeValue_head, eval_syscallIsZero, eval_syscallU16toU8, ProvableType.eval_field, ProvableType.getElem_eval_fields,
    List.forall_append, List.Forall,
    ProvableStruct.structEvalLiteralProc, Expression.eval, eval_sub,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero, sub_zero, zero_sub, zero_add, mul_neg,
    neg_eq_zero,
    true_and, and_assoc]
  constructor
  · rintro ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hE9, hE12, hE16, hE23, hE27, hE29, hE31, hE33, hE36, hE43,
      hE50, hE55, hE60, rest⟩
    obtain ⟨hE64, hE68, hE70, hE72, hE74, hE75, hE76, hE78, hE82, hE83, hE84, hE88, hE91, hE93, hE94, hE95,
      hE99, hE102, hE107, hE110, rest⟩ := rest
    obtain ⟨hE113, hE116, hE121, hE124, hE127, hE130, hE134, hE136, hE139, hE143, hE147, hE151, hE155,
      hE159, hE163, hE167, hE172, hE176, hE179, hE182, rest⟩ := rest
    obtain ⟨hE185, hE188, hE191, hE194, hE197, hE200, hE205, hE275, hE277, hE279, hE281, hE283, hE286,
      hE289, hE292, hE295, hE322, hE324, hE325, hE326, hE336⟩ := rest
    exact ⟨hE9, hE275, hE93, hE82, hE78, hE16, hb0, hb3, hb4, hb5, hb6, hE12, hE70, hE72, hE74,
      hE23, hE36, hE43, hE50, hE55, hE27, hE29, hE31, hE33, hE107, hE110, hE113, hE116, hE121,
      hE124, hE127, hE130, hE60, hE64, hE68, hE324, hE325, hE326, hE75, hE76, hE83, hE84, hb1,
      hE88, hE91, hE94, hE95, hb2, hE99, hE102, hE139, hE143, hE147, hE151, hE155, hE159, hE163,
      hE167, hE172, hE176, hE179, hE182, hE185, hE188, hE191, hE194, hE197, hE200, hE205,
      by linear_combination hE286 - (Expression.eval env r.is_real) * hE277 - (Expression.eval env r.is_real * 256) * hE279,
      by linear_combination hE289 - (Expression.eval env r.is_real) * hE281 - (Expression.eval env r.is_real * 256) * hE283,
      hE292, hE295, hE134, hE136, hE277, hE279, hE281, hE283, hE322, hE336⟩
  · rintro ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, rest⟩
    obtain ⟨n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38,
      n39, rest⟩ := rest
    obtain ⟨n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58,
      n59, rest⟩ := rest
    obtain ⟨n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, c0, c1, c2, c3, c4, c5, c6,
      c7⟩ := rest
    exact ⟨n6, n42, n47, n7, n8, n9, n10, n0, n11, n5, n15, n20, n21, n22, n23, n16, n17, n18,
      n19, n32, n33, n34, n12, n13, n14, n38, n39, n4, n3, n40, n41, n43, n44, n2, n45, n46, n48,
      n49, n24, n25, n26, n27, n28, n29, n30, n31, c0, c1, n50, n51, n52, n53, n54, n55, n56,
      n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n1, c2, c3, c4, c5,
      by linear_combination n69 + (Expression.eval env r.is_real) * c2 + (Expression.eval env r.is_real * 256) * c3,
      by linear_combination n70 + (Expression.eval env r.is_real) * c4 + (Expression.eval env r.is_real * 256) * c5,
      n71, n72, c6, n35, n36, n37, c7⟩
/-! ## The native interaction list, block by block

The interaction counterpart of `syscallInstrsAssertBlocks`, proved the same structural way and for
the same reason. Note the group SP1 does not have: the `Exit` push and the seven `PublicValues`
pulls are the native-only hand-off that carries `PublicValueBinding`. The generic syscall send is
*not* in that group — SP1 emits it too, and the native channel is named so that both project to the
same `LookupAccess` key. -/

/-- The row's complete emitted interaction list, split into its sixteen composed blocks and its own
three groups: the Program fetch with the three register Memory pairs, the six byte checks, and the
public-value hand-off followed by the generic syscall send. -/
theorem syscallInstrsInteractionBlocks (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions ((SyscallInstrsChip.main r).operations offset) =
      Operations.interactions
        ((SP1Clean.U16toU8OperationSafe.circuit.main
          ⟨r.op_a_memory.prev_value, r.syscall_id_bytes, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst haltCode, r.is_halt_zero, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst enterUnconstrainedCode, r.is_enter_unconstrained,
           r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst hintLenCode, r.is_hint_len, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst commitCode, r.is_commit, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SP1Clean.IsZeroOperation.circuit.main
          ⟨syscallIdVar r - natConst commitDeferredCode, r.is_commit_deferred, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((Readers.CPUState.circuit.main ⟨r.state, r.next_pc, 264, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_a_memory, r.is_real, clkLowVar r + 4⟩).operations offset) ++
      Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_b_memory, r.is_real, clkLowVar r + 3⟩).operations offset) ++
      Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main ⟨r.op_c_memory, r.is_real, clkLowVar r + 2⟩).operations offset) ++
      [({ mult := -r.is_real, msg := programMsg r,
          assumeGuarantees := true } :
         ChannelInteraction (programChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := memPullMsg r r.op_a_memory r.op_a,
          assumeGuarantees := true } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := r.is_real, msg := memPushMsg r r.op_a 4 r.op_a_value,
          assumeGuarantees := false } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := memPullMsg r r.op_b_memory r.op_b,
          assumeGuarantees := true } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := r.is_real, msg := memPushMsg r r.op_b 3 r.op_b_memory.prev_value,
          assumeGuarantees := false } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := memPullMsg r r.op_c_memory r.op_c,
          assumeGuarantees := true } :
         ChannelInteraction (memoryChannel (p := p))).toRaw,
       ({ mult := r.is_real, msg := memPushMsg r r.op_c 2 r.op_c_memory.prev_value,
          assumeGuarantees := false } :
         ChannelInteraction (memoryChannel (p := p))).toRaw] ++
      Operations.interactions
        ((SyscallInstrsChip.WriteArm.circuit.main
          ⟨r.op_a_memory.prev_value, r.op_a_value, r.op_a_0,
           r.is_enter_unconstrained.result, r.is_hint_len.result, r.is_real⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.PcArm.circuit.main ⟨r.state.pc, r.next_pc, r.is_real, r.is_halt⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.DispatchArm.circuit.main
          ⟨r.op_b_memory.prev_value, r.op_c_memory.prev_value, tableByteVar r⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.FieldBoundArm.circuit.main
          ⟨r.op_b_memory.prev_value, r.op_b_cmp.bit, r.is_halt⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.FieldBoundArm.circuit.main
          ⟨r.op_c_memory.prev_value, r.op_c_cmp.bit, r.is_commit_deferred.result⟩).operations offset) ++
      Operations.interactions
        ((SyscallInstrsChip.CommitArm.circuit.main
          ⟨r.digest_index_bits, r.digest_word, r.op_b_memory.prev_value,
           r.op_c_memory.prev_value, r.is_commit.result, r.is_commit_deferred.result,
           r.is_real⟩).operations offset) ++
      [({ mult := -r.is_real, msg := (⟨6, r.op_a_value[0], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[1], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[2], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[3], natConst 16, 0⟩ : ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := (⟨3, 0, r.digest_word[0], r.digest_word[1]⟩ :
            ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := (⟨3, 0, r.digest_word[2], r.digest_word[3]⟩ :
            ByteRow (Expression (ZMod p))),
          assumeGuarantees := true } :
         ChannelInteraction (byteChannel (p := p))).toRaw] ++
      [({ mult := r.is_halt, msg := exitMsg r,
          assumeGuarantees := false } :
         ChannelInteraction (exitChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨natConst 145, 1⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit_deferred.result, msg := ⟨natConst 147, 1⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 0, r.digest_word[0]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 1, r.digest_word[1]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 2, r.digest_word[2]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 3, r.digest_word[3]⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := -(r.is_real * r.is_commit_deferred.result), msg := ⟨selectedIndex r 72 1, reduceWord r.op_c_memory.prev_value⟩,
          assumeGuarantees := true } :
         ChannelInteraction (publicValuesChannel (p := p))).toRaw,
       ({ mult := tableByteVar r, msg := syscallMsg r,
          assumeGuarantees := false } :
         ChannelInteraction (syscallChannel (p := p))).toRaw] := by
  simp only [SyscallInstrsChip.main, Circuit.operations, Circuit.bind_def,
    assertZero, subcircuitWithAssertion, assertion, Channel.pullIf, Channel.pushIf,
    Operations.interactions_assert,
    Operations.interactions_interact, Operations.interactions_nil,
    Operations.interactions_subcircuit,
    FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_localLength, GeneralFormalCircuit.toSubcircuit_localLength,
    Readers.CPUState.circuit_localLength, Readers.RegisterAccessCols.circuit_localLength,
    SP1Clean.IsZeroOperation.circuit_localLength,
    SyscallInstrsChip.PcArm.circuit_localLength,
    SyscallInstrsChip.WriteArm.circuit_localLength,
    SyscallInstrsChip.FieldBoundArm.circuit_localLength,
    SyscallInstrsChip.DispatchArm.circuit_localLength,
    SP1Clean.U16toU8OperationSafe.circuit_localLength,
    Operations.localLength, Nat.add_zero,
    List.append_assoc, List.cons_append, List.nil_append]

/-! ## Each composed block's interaction list

Again one lemma per composed circuit over an opaque input. Four of the sixteen blocks emit nothing:
`IsZeroOperation` and three of the five arms are pure `assertZero` gadgets. -/

omit [Fact (2 ^ 17 < p)] in
/-- The five arm selectors emit nothing: `IsZeroOperation` is a pure `assertZero` gadget, and so is
the scalar equality gadget it composes. -/
theorem isZeroInteractions (input : Var SP1Clean.IsZeroOperation.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
      ((SP1Clean.IsZeroOperation.circuit.main input).operations offset) = [] := by
  simp only [SP1Clean.IsZeroOperation.circuit, SP1Clean.IsZeroOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main]

omit [Fact (2 ^ 17 < p)] in
/-- `PcArm`, `WriteArm`, `DispatchArm` and `CommitArm` are pure `assertZero` blocks. -/
theorem pcArmInteractions (input : Var SyscallInstrsChip.PcArm.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.PcArm.circuit.main input).operations offset) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
theorem writeArmInteractions (input : Var SyscallInstrsChip.WriteArm.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.WriteArm.circuit.main input).operations offset) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
theorem dispatchArmInteractions (input : Var SyscallInstrsChip.DispatchArm.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.DispatchArm.circuit.main input).operations offset) = [] := rfl

omit [Fact (2 ^ 17 < p)] in
theorem commitArmInteractions (input : Var SyscallInstrsChip.CommitArm.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
      ((SyscallInstrsChip.CommitArm.circuit.main input).operations offset) = [] := rfl

/-- SP1's `slice_range_check_u8` on the four split bytes. -/
theorem u16toU8SafeInteractions (input : Var SP1Clean.U16toU8OperationSafe.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((SP1Clean.U16toU8OperationSafe.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[0],
            (input.u16_values[0] - input.cols.low_bytes[0]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[1],
            (input.u16_values[1] - input.cols.low_bytes[1]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[2],
            (input.u16_values[2] - input.cols.low_bytes[2]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.low_bytes[3],
            (input.u16_values[3] - input.cols.low_bytes[3]) *
              Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [SP1Clean.U16toU8OperationSafe.circuit, SP1Clean.U16toU8OperationSafe.main, circuit_norm]

/-- The `U16Compare` bound: one range check, then a pure equality. -/
theorem u16CompareInteractions (input : Var SP1Clean.U16CompareOperation.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((SP1Clean.U16CompareOperation.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨6, input.a - input.b + input.cols.bit * 65536, Expression.const ((16 : ℕ) : ZMod p),
            0⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [SP1Clean.U16CompareOperation.circuit, SP1Clean.U16CompareOperation.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main]

/-- The `FieldBoundArm`'s only bus traffic is its `U16Compare` fragment's. -/
theorem fieldBoundArmInteractions (input : Var SyscallInstrsChip.FieldBoundArm.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((SyscallInstrsChip.FieldBoundArm.circuit.main input).operations offset) =
      Operations.interactions
        ((SP1Clean.U16CompareOperation.circuit.main
            ⟨input.word[1], Expression.const ((fieldLimbBound : ℕ) : ZMod p), ⟨input.bit⟩,
             input.is_real⟩).operations offset) := by
  simp only [SyscallInstrsChip.FieldBoundArm.circuit, SyscallInstrsChip.FieldBoundArm.main,
    circuit_norm, FormalAssertion.toSubcircuit_interactions]

/-- The state reader's two clock range checks and its State edge. -/
theorem cpuStateInteractions (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions ((Readers.CPUState.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨6, (input.cols.clk_0_16 - 1) * Expression.const (8 : ZMod p)⁻¹,
            Expression.const ((13 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, input.cols.clk_16_24, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
       (stateChannel.pulledIf input.is_real (Readers.CPUState.currentMsg input)).toRaw,
       (stateChannel.pushedIf input.is_real (Readers.CPUState.nextMsg input)).toRaw] := by
  simp only [Readers.CPUState.circuit, Readers.CPUState.main, circuit_norm]

/-- The register reader's two timestamp range checks. -/
theorem registerAccessTimestampInteractions
    (input : Var Readers.RegisterAccessTimestamp.Inputs (ZMod p)) (offset : ℕ) :
    Operations.interactions
        ((Readers.RegisterAccessTimestamp.circuit.main input).operations offset) =
      [(byteChannel.pulledIf input.is_real
          (⟨6, input.cols.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
            ByteRow (Expression (ZMod p)))).toRaw,
       (byteChannel.pulledIf input.is_real
          (⟨3, 0, (input.clk_target - input.cols.prev_low - 1 - input.cols.diff_low_limb) *
            Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw] := by
  simp only [Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    circuit_norm]

theorem registerAccessColsInteractions (input : Var Readers.RegisterAccessCols.Inputs (ZMod p))
    (offset : ℕ) :
    Operations.interactions
        ((Readers.RegisterAccessCols.circuit.main input).operations offset) =
      Operations.interactions
        ((Readers.RegisterAccessTimestamp.circuit.main
            ⟨input.cols.access_timestamp, input.is_real, input.clk_target⟩).operations offset) := by
  simp only [Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main, circuit_norm,
    FormalAssertion.toSubcircuit_interactions]

/-! ## The row's traffic, one bus at a time

`nativeAccesses` reads the row bus by bus, so these four lists plus the native-only tail are what it
is built from. Each follows from the block decomposition by filtering, which is why the channel
distinctness matrix in `Model/Channels.lean` had to grow the three newer buses first. -/

/-- The State edge: pull `(clk, pc)`, push `(clk + 264, next_pc)`. -/
theorem syscallInstrsInteractionsWith_state (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (stateChannel (p := p)).toRaw =
    [(stateChannel.pulledIf r.is_real
        (Readers.CPUState.currentMsg ⟨r.state, r.next_pc, 264, r.is_real⟩)).toRaw,
     (stateChannel.pushedIf r.is_real
        (Readers.CPUState.nextMsg ⟨r.state, r.next_pc, 264, r.is_real⟩)).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_stateChannel_false,
    Channels.memoryChannel_eq_stateChannel_false,
    Channels.programChannel_eq_stateChannel_false,
    Channels.exitChannel_eq_stateChannel_false,
    Channels.syscallChannel_eq_stateChannel_false,
    Channels.publicValuesChannel_eq_stateChannel_false]

/-- The single committed `ECALL` fetch. -/
theorem syscallInstrsInteractionsWith_program (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (programChannel (p := p)).toRaw =
    [
      ({ mult := -r.is_real, msg := programMsg r,
         assumeGuarantees := true } :
        ChannelInteraction (programChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_programChannel_false,
    Channels.stateChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    Channels.exitChannel_eq_programChannel_false,
    Channels.syscallChannel_eq_programChannel_false,
    Channels.publicValuesChannel_eq_programChannel_false]

/-- The three register access pairs, read-prior pulled and read-back pushed. -/
theorem syscallInstrsInteractionsWith_memory (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (memoryChannel (p := p)).toRaw =
    [
      ({ mult := -r.is_real, msg := memPullMsg r r.op_a_memory r.op_a,
         assumeGuarantees := true } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := r.is_real, msg := memPushMsg r r.op_a 4 r.op_a_value,
         assumeGuarantees := false } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := memPullMsg r r.op_b_memory r.op_b,
         assumeGuarantees := true } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := r.is_real, msg := memPushMsg r r.op_b 3 r.op_b_memory.prev_value,
         assumeGuarantees := false } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := memPullMsg r r.op_c_memory r.op_c,
         assumeGuarantees := true } :
        ChannelInteraction (memoryChannel (p := p))).toRaw,
      ({ mult := r.is_real, msg := memPushMsg r r.op_c 2 r.op_c_memory.prev_value,
         assumeGuarantees := false } :
        ChannelInteraction (memoryChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.stateChannel_eq_memoryChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    Channels.exitChannel_eq_memoryChannel_false,
    Channels.syscallChannel_eq_memoryChannel_false,
    Channels.publicValuesChannel_eq_memoryChannel_false]

/-- The `Exit` hand-off: a single `is_halt`-gated push of the reduced exit code. Unlike the halt
table's, there is no anti-gated companion push — a many-row table cannot use that trick. -/
theorem syscallInstrsInteractionsWith_exit (r : Var SyscallInstrsChip.Inputs (ZMod p))
    (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (exitChannel (p := p)).toRaw =
    [({ mult := r.is_halt, msg := SyscallInstrsChip.exitMsg r, assumeGuarantees := false } :
        ChannelInteraction (exitChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.byteChannel_eq_exitChannel_false,
    Channels.stateChannel_eq_exitChannel_false,
    Channels.programChannel_eq_exitChannel_false,
    Channels.memoryChannel_eq_exitChannel_false,
    Channels.syscallChannel_eq_exitChannel_false,
    Channels.publicValuesChannel_eq_exitChannel_false]

/-- Twenty byte checks: the four identifier-split bytes, the state reader's two clock bounds, two timestamp bounds per register, one field-element compare per bounded operand, the four `op_a_value` range checks, and the two digest byte pairs. -/
theorem syscallInstrsInteractionsWith_byte (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    ((SyscallInstrsChip.main r).operations offset).interactionsWith (byteChannel (p := p)).toRaw =
    [
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[0],
          (r.op_a_memory.prev_value[0] - r.syscall_id_bytes.low_bytes[0]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[1],
          (r.op_a_memory.prev_value[1] - r.syscall_id_bytes.low_bytes[1]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[2],
          (r.op_a_memory.prev_value[2] - r.syscall_id_bytes.low_bytes[2]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.syscall_id_bytes.low_bytes[3],
          (r.op_a_memory.prev_value[3] - r.syscall_id_bytes.low_bytes[3]) *
            Expression.const (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, (r.state.clk_0_16 - 1) * Expression.const (8 : ZMod p)⁻¹,
          Expression.const ((13 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0, r.state.clk_16_24, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, r.op_a_memory.access_timestamp.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0,
          (clkLowVar r + 4 - r.op_a_memory.access_timestamp.prev_low - 1 -
            r.op_a_memory.access_timestamp.diff_low_limb) * Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, r.op_b_memory.access_timestamp.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0,
          (clkLowVar r + 3 - r.op_b_memory.access_timestamp.prev_low - 1 -
            r.op_b_memory.access_timestamp.diff_low_limb) * Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨6, r.op_c_memory.access_timestamp.diff_low_limb, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_real
        (⟨3, 0,
          (clkLowVar r + 2 - r.op_c_memory.access_timestamp.prev_low - 1 -
            r.op_c_memory.access_timestamp.diff_low_limb) * Expression.const (65536 : ZMod p)⁻¹, 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_halt
        (⟨6, r.op_b_memory.prev_value[1] - Expression.const ((fieldLimbBound : ℕ) : ZMod p) +
          r.op_b_cmp.bit * 65536, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      (byteChannel.pulledIf r.is_commit_deferred.result
        (⟨6, r.op_c_memory.prev_value[1] - Expression.const ((fieldLimbBound : ℕ) : ZMod p) +
          r.op_c_cmp.bit * 65536, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[0], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[1], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[2], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_real, msg := (⟨6, r.op_a_value[3], natConst 16, 0⟩ :
          ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result,
         msg := (⟨3, 0, r.digest_word[0], r.digest_word[1]⟩ :
           ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result,
         msg := (⟨3, 0, r.digest_word[2], r.digest_word[3]⟩ :
           ByteRow (Expression (ZMod p))), assumeGuarantees := true } :
        ChannelInteraction (byteChannel (p := p))).toRaw] := by
  simp only [Operations.interactionsWith, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, decide_eq_true_eq, if_true, if_false,
    Channels.stateChannel_eq_byteChannel_false,
    Channels.memoryChannel_eq_byteChannel_false,
    Channels.programChannel_eq_byteChannel_false,
    Channels.exitChannel_eq_byteChannel_false,
    Channels.syscallChannel_eq_byteChannel_false,
    Channels.publicValuesChannel_eq_byteChannel_false]

/-- The three buses outside `nativeAccesses`'s four-way grouping: the `Exit` push, the seven
`PublicValues` pulls, and the generic syscall send. The first eight are the native-only hand-off
carrying `PublicValueBinding`. The ninth is SP1's own bus — `nativeAccesses` groups by *channel*
rather than by kind, so it lands here even though `InteractionKind.Syscall` classifies it. -/
theorem syscallInstrsUnexpectedInteractions (r : Var SyscallInstrsChip.Inputs (ZMod p))
    (offset : ℕ) :
    unexpectedInteractions ((SyscallInstrsChip.main r).operations offset) =
    [
      ({ mult := r.is_halt, msg := exitMsg r,
         assumeGuarantees := false } :
        ChannelInteraction (exitChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result, msg := ⟨natConst 145, 1⟩,
         assumeGuarantees := true } :
        ChannelInteraction (publicValuesChannel (p := p))).toRaw,
      ({ mult := -r.is_commit_deferred.result, msg := ⟨natConst 147, 1⟩,
         assumeGuarantees := true } :
        ChannelInteraction (publicValuesChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 0, r.digest_word[0]⟩,
         assumeGuarantees := true } :
        ChannelInteraction (publicValuesChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 1, r.digest_word[1]⟩,
         assumeGuarantees := true } :
        ChannelInteraction (publicValuesChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 2, r.digest_word[2]⟩,
         assumeGuarantees := true } :
        ChannelInteraction (publicValuesChannel (p := p))).toRaw,
      ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 3, r.digest_word[3]⟩,
         assumeGuarantees := true } :
        ChannelInteraction (publicValuesChannel (p := p))).toRaw,
      ({ mult := -(r.is_real * r.is_commit_deferred.result), msg := ⟨selectedIndex r 72 1, reduceWord r.op_c_memory.prev_value⟩,
         assumeGuarantees := true } :
        ChannelInteraction (publicValuesChannel (p := p))).toRaw,
      ({ mult := tableByteVar r, msg := syscallMsg r,
         assumeGuarantees := false } :
        ChannelInteraction (syscallChannel (p := p))).toRaw] := by
  simp only [unexpectedInteractions, syscallInstrsInteractionBlocks, isZeroInteractions,
    pcArmInteractions, writeArmInteractions, dispatchArmInteractions, commitArmInteractions,
    u16toU8SafeInteractions, u16CompareInteractions, fieldBoundArmInteractions,
    cpuStateInteractions, registerAccessColsInteractions, registerAccessTimestampInteractions,
    ChannelInteraction.toRaw_channel,
    List.filter_cons, List.filter_nil, List.append_nil, List.nil_append,
    List.cons_append, if_true, if_false, ne_eq,
    Channels.byteChannel_eq_stateChannel_false,
    Channels.byteChannel_eq_memoryChannel_false,
    Channels.byteChannel_eq_programChannel_false,
    Channels.stateChannel_eq_byteChannel_false,
    Channels.stateChannel_eq_memoryChannel_false,
    Channels.stateChannel_eq_programChannel_false,
    Channels.memoryChannel_eq_stateChannel_false,
    Channels.memoryChannel_eq_byteChannel_false,
    Channels.memoryChannel_eq_programChannel_false,
    Channels.programChannel_eq_stateChannel_false,
    Channels.programChannel_eq_byteChannel_false,
    Channels.programChannel_eq_memoryChannel_false,
    Channels.exitChannel_eq_stateChannel_false,
    Channels.exitChannel_eq_byteChannel_false,
    Channels.exitChannel_eq_memoryChannel_false,
    Channels.exitChannel_eq_programChannel_false,
    Channels.syscallChannel_eq_stateChannel_false,
    Channels.syscallChannel_eq_byteChannel_false,
    Channels.syscallChannel_eq_memoryChannel_false,
    Channels.syscallChannel_eq_programChannel_false,
    Channels.publicValuesChannel_eq_stateChannel_false,
    Channels.publicValuesChannel_eq_byteChannel_false,
    Channels.publicValuesChannel_eq_memoryChannel_false,
    Channels.publicValuesChannel_eq_programChannel_false,
    not_false_eq_true, not_true_eq_false, and_self, and_true, true_and, decide_true, decide_false,
    Bool.false_eq_true]

/-! ## Projecting the row's traffic to `LookupAccess`

The four SP1 buses already have `toAccess` bridges in `Model/InteractionProjection.lean`, but stated
with the channel as a named implicit; the row's own interaction lists carry it in dot-notation
position, and simp matches syntactically. These restate them once in the shape the lists use, the
way `Faithful/CPUState.lean` does inline. -/

omit [Fact (2 ^ 17 < p)] in
private theorem toAccessPulledState (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : Channels.StateMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env ((stateChannel.pulledIf gate msg).toRaw) =
      (InteractionKind.State, "SP1State",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val],
        signedVal (Expression.eval env (-gate))) :=
  toAccess_pullIf_state env gate msg

omit [Fact (2 ^ 17 < p)] in
private theorem toAccessPushedState (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : Channels.StateMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env ((stateChannel.pushedIf mult msg).toRaw) =
      (InteractionKind.State, "SP1State",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val],
        signedVal (Expression.eval env mult)) :=
  toAccess_pushIf_state env mult msg

omit [Fact (2 ^ 17 < p)] in
/-- The same bridge at the `pulledIf` spelling. The row's byte list carries both: entries that come
from a composed reader arrive folded, entries the row emits itself arrive as the raw record. -/
private theorem toAccessPulledByteMsg (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : ByteRow (Expression (ZMod p))) :
    AbstractInteraction.toAccess env ((byteChannel.pulledIf gate msg).toRaw) =
      (InteractionKind.Byte, "SP1Byte",
        [(Expression.eval env msg.opcode).val, (Expression.eval env msg.a).val,
         (Expression.eval env msg.b).val, (Expression.eval env msg.c).val],
        signedVal (Expression.eval env (-gate))) :=
  toAccess_pullIf_byte env gate msg

omit [Fact (2 ^ 17 < p)] in
private theorem toAccessPulledByte (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : ByteRow (Expression (ZMod p))) :
    AbstractInteraction.toAccess env
        (({ mult := -gate, msg := msg, assumeGuarantees := true } :
          ChannelInteraction (byteChannel (p := p))).toRaw) =
      (InteractionKind.Byte, "SP1Byte",
        [(Expression.eval env msg.opcode).val, (Expression.eval env msg.a).val,
         (Expression.eval env msg.b).val, (Expression.eval env msg.c).val],
        signedVal (Expression.eval env (-gate))) :=
  toAccess_pullIf_byte env gate msg

omit [Fact (2 ^ 17 < p)] in
private theorem toAccessPushedSyscall (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : Channels.SyscallMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env
        (({ mult := mult, msg := msg, assumeGuarantees := false } :
          ChannelInteraction (syscallChannel (p := p))).toRaw) =
      (InteractionKind.Syscall, "SP1Syscall",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.syscall_id).val, (Expression.eval env msg.arg1[0]).val,
         (Expression.eval env msg.arg1[1]).val, (Expression.eval env msg.arg1[2]).val,
         (Expression.eval env msg.arg2[0]).val, (Expression.eval env msg.arg2[1]).val,
         (Expression.eval env msg.arg2[2]).val],
        signedVal (Expression.eval env mult)) :=
  toAccess_pushIf_syscall env mult msg

omit [Fact (2 ^ 17 < p)] in
private theorem toAccessPulledProgram (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : ProgramMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env
        (({ mult := -gate, msg := msg, assumeGuarantees := true } :
          ChannelInteraction (programChannel (p := p))).toRaw) =
      (InteractionKind.Program, "SP1Program",
        [(Expression.eval env msg.pc0).val, (Expression.eval env msg.pc1).val,
         (Expression.eval env msg.pc2).val, (Expression.eval env msg.opcode).val,
         (Expression.eval env msg.op_a).val, (Expression.eval env msg.op_b[0]).val,
         (Expression.eval env msg.op_b[1]).val, (Expression.eval env msg.op_b[2]).val,
         (Expression.eval env msg.op_b[3]).val, (Expression.eval env msg.op_c[0]).val,
         (Expression.eval env msg.op_c[1]).val, (Expression.eval env msg.op_c[2]).val,
         (Expression.eval env msg.op_c[3]).val, (Expression.eval env msg.op_a_0).val,
         (Expression.eval env msg.imm_b).val, (Expression.eval env msg.imm_c).val],
        signedVal (Expression.eval env (-gate))) :=
  toAccess_pullIf_program env gate msg

omit [Fact (2 ^ 17 < p)] in
private theorem toAccessPulledMemory (env : Environment (ZMod p)) (gate : Expression (ZMod p))
    (msg : MemoryMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env
        (({ mult := -gate, msg := msg, assumeGuarantees := true } :
          ChannelInteraction (memoryChannel (p := p))).toRaw) =
      (InteractionKind.Memory, "SP1Memory",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.addr0).val, (Expression.eval env msg.addr1).val,
         (Expression.eval env msg.addr2).val, (Expression.eval env msg.value[0]).val,
         (Expression.eval env msg.value[1]).val, (Expression.eval env msg.value[2]).val,
         (Expression.eval env msg.value[3]).val],
        signedVal (Expression.eval env (-gate))) :=
  toAccess_pullIf_memory env gate msg

omit [Fact (2 ^ 17 < p)] in
private theorem toAccessPushedMemory (env : Environment (ZMod p)) (mult : Expression (ZMod p))
    (msg : MemoryMsg (Expression (ZMod p))) :
    AbstractInteraction.toAccess env
        (({ mult := mult, msg := msg, assumeGuarantees := false } :
          ChannelInteraction (memoryChannel (p := p))).toRaw) =
      (InteractionKind.Memory, "SP1Memory",
        [(Expression.eval env msg.clk_high).val, (Expression.eval env msg.clk_low).val,
         (Expression.eval env msg.addr0).val, (Expression.eval env msg.addr1).val,
         (Expression.eval env msg.addr2).val, (Expression.eval env msg.value[0]).val,
         (Expression.eval env msg.value[1]).val, (Expression.eval env msg.value[2]).val,
         (Expression.eval env msg.value[3]).val],
        signedVal (Expression.eval env mult)) :=
  toAccess_pushIf_memory env mult msg

/-! ## `ProvableStruct.eval` at the row's carriers

The oracle side of every bus comparison lands on `(ProvableStruct.eval env x).field` where the
native side has `Expression.eval env x.field`. These are the component-wise lemmas above, restated
at `ProvableStruct.eval` and with the scalar fields pushed through `eval_field`, so a bus comparison
does not have to bridge each projection by hand. -/

omit [Fact (2 ^ 17 < p)] in
private theorem structEvalCPUState (env : Environment (ZMod p))
    (c : Var Circuits.Types.CPUState (ZMod p)) :
    ProvableStruct.eval env c =
      ({ clk_high := Expression.eval env c.clk_high,
         clk_16_24 := Expression.eval env c.clk_16_24,
         clk_0_16 := Expression.eval env c.clk_0_16,
         pc := Eval.eval env c.pc } : Circuits.Types.CPUState (ZMod p)) := by
  rw [← ProvableStruct.eval_eq_eval, eval_syscallCPUState]
  simp only [ProvableType.eval_field]

omit [Fact (2 ^ 17 < p)] in
private theorem structEvalAccess (env : Environment (ZMod p))
    (a : Var Circuits.Types.RegisterAccessCols (ZMod p)) :
    ProvableStruct.eval env a =
      ({ prev_value := Eval.eval env a.prev_value
         access_timestamp := Eval.eval env a.access_timestamp } :
        Circuits.Types.RegisterAccessCols (ZMod p)) := by
  rw [← ProvableStruct.eval_eq_eval, eval_syscallAccess]

omit [Fact (2 ^ 17 < p)] in
private theorem structEvalU16toU8 (env : Environment (ZMod p))
    (u : Var Circuits.Types.U16toU8Operation (ZMod p)) :
    ProvableStruct.eval env u =
      ({ low_bytes := Eval.eval env u.low_bytes } : Circuits.Types.U16toU8Operation (ZMod p)) := by
  rw [← ProvableStruct.eval_eq_eval, eval_syscallU16toU8]

/-! ## Bus by bus, against the extracted oracle

The four SP1 instruction buses, compared block for block. Memory and Program carry the project-wide
polarity flip — SP1 `.send`s the read-prior record and the Program fetch where the native circuit
pulls them — so `nativeAccesses` negates both, and the comparison is stated after that negation. -/

/-- **State.** The row's clock/pc edge, entry for entry. -/
theorem syscallInstrsStateAccesses (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    (((SyscallInstrsChip.main r).operations offset).interactionsWith
        stateChannel.toRaw).map (AbstractInteraction.toAccess env)
      = ((Extracted.SyscallInstrsCols.interactions (syscallInstrsRustColumns env r) preprocessed
          publicValues).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.State) := by
  rw [syscallInstrsInteractionsWith_state]
  simp only [toAccessPulledState, toAccessPushedState, Readers.CPUState.currentMsg,
    Readers.CPUState.nextMsg, Expression.eval, neg_one_mul,
    Extracted.SyscallInstrsCols.interactions, syscallInstrsRustColumns,
    Extracted.U16toU8OperationSafe.interactions, Extracted.IsZeroOperation.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Extracted.AirInteractionKind.lookupKind_syscall,
    Extracted.AirInteractionKind.lookupTable_syscall,
    List.map_cons, List.map_nil, List.filter_cons,
    List.filter_nil, List.append_nil, List.nil_append, List.cons_append,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero,
    decide_eq_true_eq, if_true, if_false, reduceCtorEq]

/-- **Program.** The single committed `ECALL` fetch. SP1 sends it where the native row pulls it, so
the comparison carries the project-wide Program polarity flip as a `negMult` on the oracle side —
the same shape `Faithful/AddChip.lean` uses. -/
theorem syscallInstrsProgramAccesses (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    (((SyscallInstrsChip.main r).operations offset).interactionsWith
        programChannel.toRaw).map (AbstractInteraction.toAccess env)
      = (((Extracted.SyscallInstrsCols.interactions (syscallInstrsRustColumns env r) preprocessed
          publicValues).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Program)).map LookupAccessList.negMult := by
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  rw [syscallInstrsInteractionsWith_program]
  simp [toAccessPulledProgram, SyscallInstrsChip.programMsg, LookupAccessList.negMult,
    signedVal_neg hp2, Opcode.ofNat,
    Extracted.SyscallInstrsCols.interactions, syscallInstrsRustColumns,
    Extracted.U16toU8OperationSafe.interactions, Extracted.IsZeroOperation.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · -- the committed `ECALL` discriminant is literal under the ambient field bound
    have hp := Fact.out (p := 2 ^ 17 < p)
    rw [show Expression.eval env (50 : Expression (ZMod p)) = ((50 : ℕ) : ZMod p) from by norm_cast,
      ZMod.val_natCast_of_lt (show (50 : ℕ) < p by omega)]
  · rw [eval_neg, signedVal_neg hp2]

/-- **Memory.** The three register access pairs, in the row's own order — `t0`, `a0`, `a1`, each a
read-prior followed by a read-back. Same polarity flip as Program: SP1 sends the prior record where
the native row pulls it. -/
theorem syscallInstrsMemoryAccesses (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    (((SyscallInstrsChip.main r).operations offset).interactionsWith
        memoryChannel.toRaw).map (AbstractInteraction.toAccess env)
      = (((Extracted.SyscallInstrsCols.interactions (syscallInstrsRustColumns env r) preprocessed
          publicValues).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Memory)).map LookupAccessList.negMult := by
  have hp2 : 2 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  rw [syscallInstrsInteractionsWith_memory]
  simp [toAccessPulledMemory, toAccessPushedMemory, SyscallInstrsChip.memPullMsg,
    SyscallInstrsChip.memPushMsg, SyscallInstrsChip.clkLowVar, LookupAccessList.negMult,
    signedVal_neg hp2, Expression.eval,
    Extracted.SyscallInstrsCols.interactions, syscallInstrsRustColumns,
    Extracted.U16toU8OperationSafe.interactions, Extracted.IsZeroOperation.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign]

omit [Fact (2 ^ 17 < p)] in
/-- The extracted oracle's `Syscall` block: exactly one send, at the identifier's table byte.
Stated over an opaque row so the thirty-entry interaction list is normalised once, against nothing
else. -/
private theorem syscallInstrsRustSyscallBlock (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (cols : Extracted.SyscallInstrsCols (ZMod p)) :
    ((Extracted.SyscallInstrsCols.interactions cols preprocessed publicValues).map
        Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Syscall)
      = [(InteractionKind.Syscall, "SP1Syscall",
          [cols.values[0].val, (cols.values[2] + cols.values[1] * 65536).val,
           (Extracted.U16toU8OperationSafe.value
             #v[cols.values[7], cols.values[8], cols.values[9], cols.values[10]]
             { low_bytes := #v[cols.values[36], cols.values[37], cols.values[38],
                               cols.values[39]] } cols.values[64])[0].val,
           cols.values[15].val, cols.values[16].val, cols.values[17].val,
           cols.values[22].val, cols.values[23].val, cols.values[24].val],
          signedVal (Extracted.U16toU8OperationSafe.value
            #v[cols.values[7], cols.values[8], cols.values[9], cols.values[10]]
            { low_bytes := #v[cols.values[36], cols.values[37], cols.values[38],
                              cols.values[39]] } cols.values[64])[1])] := by
  -- unfold only the four `@[irreducible]` oracle definitions, then let the kernel compute.
  -- Doing the list/filter/kind reduction in `simp` instead builds one monolithic congruence term
  -- and hits the kernel size cliff: the same goal does not terminate that way as a named theorem,
  -- and takes two seconds this way. `example` hides it — an anonymous declaration is checked more
  -- cheaply, so a probe that passes says nothing about the lemma.
  simp only [Extracted.SyscallInstrsCols.interactions,
    Extracted.U16toU8OperationSafe.interactions, Extracted.IsZeroOperation.interactions,
    Extracted.U16CompareOperation.interactions]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- The extracted oracle's `Byte` block: twenty checks. Same recipe as the `Syscall` block — unfold
only the four `@[irreducible]` oracle definitions and let `rfl` compute, so the proof term stays
small. -/
private theorem syscallInstrsRustByteBlock (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (cols : Extracted.SyscallInstrsCols (ZMod p)) :
    ((Extracted.SyscallInstrsCols.interactions cols preprocessed publicValues).map
        Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Byte)
      =
      [(InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val,
        cols.values[36].val, ((cols.values[7] - cols.values[36]) * (256 : ZMod p)⁻¹).val],
        signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val,
        cols.values[37].val, ((cols.values[8] - cols.values[37]) * (256 : ZMod p)⁻¹).val],
        signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val,
        cols.values[38].val, ((cols.values[9] - cols.values[38]) * (256 : ZMod p)⁻¹).val],
        signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val,
        cols.values[39].val, ((cols.values[10] - cols.values[39]) * (256 : ZMod p)⁻¹).val],
        signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, (cols.values[16] - (32512 : ZMod p) +
        cols.values[62] * (65536 : ZMod p)).val, (16 : ZMod p).val, (0 : ZMod p).val], signedVal
        (-cols.values[31])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, (cols.values[23] - (32512 : ZMod p) +
        cols.values[63] * (65536 : ZMod p)).val, (16 : ZMod p).val, (0 : ZMod p).val], signedVal
        (-cols.values[49])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, ((cols.values[2] - (1 : ZMod p)) * (8
        : ZMod p)⁻¹).val, (13 : ZMod p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val, cols.values[1].val,
        (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, cols.values[12].val, (16 : ZMod
        p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val, ((cols.values[2] +
        cols.values[1] * (65536 : ZMod p) + (4 : ZMod p) - cols.values[11] - (1 : ZMod p) -
        cols.values[12]) * (65536 : ZMod p)⁻¹).val, (0 : ZMod p).val], signedVal
        (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, cols.values[20].val, (16 : ZMod
        p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val, ((cols.values[2] +
        cols.values[1] * (65536 : ZMod p) + (3 : ZMod p) - cols.values[19] - (1 : ZMod p) -
        cols.values[20]) * (65536 : ZMod p)⁻¹).val, (0 : ZMod p).val], signedVal
        (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, cols.values[27].val, (16 : ZMod
        p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val, ((cols.values[2] +
        cols.values[1] * (65536 : ZMod p) + (2 : ZMod p) - cols.values[26] - (1 : ZMod p) -
        cols.values[27]) * (65536 : ZMod p)⁻¹).val, (0 : ZMod p).val], signedVal
        (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, cols.values[32].val, (16 : ZMod
        p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, cols.values[33].val, (16 : ZMod
        p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, cols.values[34].val, (16 : ZMod
        p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(6 : ZMod p).val, cols.values[35].val, (16 : ZMod
        p).val, (0 : ZMod p).val], signedVal (-cols.values[64])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val,
        cols.values[58].val, cols.values[59].val], signedVal (-cols.values[47])),
       (InteractionKind.Byte, "SP1Byte", [(3 : ZMod p).val, (0 : ZMod p).val,
        cols.values[60].val, cols.values[61].val], signedVal (-cols.values[47]))] := by
  simp only [Extracted.SyscallInstrsCols.interactions,
    Extracted.U16toU8OperationSafe.interactions, Extracted.IsZeroOperation.interactions,
    Extracted.U16CompareOperation.interactions,
    Extracted.Interaction.toAccess, Extracted.Dir.sign,
    Extracted.AirInteractionKind.lookupKind_syscall,
    Extracted.AirInteractionKind.lookupTable_syscall,
    List.map_cons, List.map_nil, List.filter_cons,
    List.filter_nil, List.append_nil, List.nil_append, List.cons_append,
    decide_eq_true_eq, if_true, if_false, reduceCtorEq,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]

omit [Fact (2 ^ 17 < p)] in
/-- **Syscall.** The generic hand-off, sent at the identifier's table byte. This is the entry the
bus classification was for: before `InteractionKind.Syscall` existed, SP1's send and the native
row's push were both labelled `State`, and the comparison could not be stated as an equality. -/
theorem syscallInstrsSyscallAccesses (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) :
    [AbstractInteraction.toAccess env
        (({ mult := tableByteVar r, msg := syscallMsg r, assumeGuarantees := false } :
          ChannelInteraction (syscallChannel (p := p))).toRaw)]
      = ((Extracted.SyscallInstrsCols.interactions (syscallInstrsRustColumns env r) preprocessed
          publicValues).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Syscall) := by
  rw [syscallInstrsRustSyscallBlock]
  simp only [toAccessPushedSyscall, SyscallInstrsChip.syscallMsg, SyscallInstrsChip.tableByteVar,
    SyscallInstrsChip.clkLowVar, SyscallInstrsChip.syscallIdVar, syscallInstrsRustColumns,
    u16toU8SafeValue_head, Expression.eval, eval_sub,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]

/-- **Byte.** Twenty checks. Unlike the other four buses this is a `Perm`, not an equality: SP1
emits the two field-element compares right after the identifier's byte split, while the native row
emits them with the arms, after the readers. Nothing else reorders, so the shuffle is one block
swap. -/
theorem syscallInstrsByteAccesses (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm
      ((((SyscallInstrsChip.main r).operations offset).interactionsWith
        byteChannel.toRaw).map (AbstractInteraction.toAccess env))
      (((Extracted.SyscallInstrsCols.interactions (syscallInstrsRustColumns env r) preprocessed
          publicValues).map Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Byte)) := by
  rw [syscallInstrsInteractionsWith_byte, syscallInstrsRustByteBlock]
  simp only [toAccessPulledByte, toAccessPulledByteMsg, syscallInstrsRustColumns,
    SyscallInstrsChip.clkLowVar,
    SyscallInstrsChip.natConst, SyscallInstrsChip.fieldLimbBound, Expression.eval,
    List.map_cons, List.map_nil, neg_one_mul, eval_sub, Nat.cast_ofNat,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
  -- the four identifier-split bytes and the last six checks are already aligned; the eight reader
  -- checks and the two field-element compares are the block that swaps.
  exact ((List.perm_append_comm (l₁ := [_, _, _, _, _, _, _, _]) (l₂ := [_, _])).append_right
    [_, _, _, _, _, _]).append_left [_, _, _, _]

/-! ## Assembling the interaction half

`nativeAccesses` groups the row by *channel*; the oracle's partition groups it by *kind*. Those
agree on the four SP1 instruction buses, and differ in exactly one place: the syscall send is a
channel of its own natively and lands in `nativeAccesses`'s unexpected tail, while on the oracle
side it is the `Syscall` block. So the assembly is the four bus comparisons, plus one element
moving past the eight native-only public-value messages. -/

omit [Fact (2 ^ 17 < p)] in
/-- The oracle carries neither native-only kind, and nothing unmodelled: its only raw interaction is
the syscall send, which is classified as a syscall. -/
private theorem syscallInstrsRustEmptyBlocks (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (cols : Extracted.SyscallInstrsCols (ZMod p)) :
    (((Extracted.SyscallInstrsCols.interactions cols preprocessed publicValues).map
        Extracted.Interaction.toAccess).filter (fun a => a.1 = InteractionKind.Exit) = [] ∧
      ((Extracted.SyscallInstrsCols.interactions cols preprocessed publicValues).map
        Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.PublicValues) = []) ∧
      ((Extracted.SyscallInstrsCols.interactions cols preprocessed publicValues).map
        Extracted.Interaction.toAccess).filter
          (fun a => a.1 = InteractionKind.Unmodelled) = [] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    (simp only [Extracted.SyscallInstrsCols.interactions,
       Extracted.U16toU8OperationSafe.interactions, Extracted.IsZeroOperation.interactions,
       Extracted.U16CompareOperation.interactions]
     rfl)

/-- The row's native-only hand-off, projected: the `Exit` push and the seven `PublicValues` pulls,
in emission order. These are the messages that carry `PublicValueBinding`; SP1 states those bindings
as row constraints against `publicValues` instead, so they have no counterpart in the oracle and the
interaction anchor carries them explicitly rather than dropping them. -/
noncomputable def syscallInstrsPublicValueAccesses (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) : LookupAccessList :=
  [AbstractInteraction.toAccess env
        ({ mult := r.is_halt, msg := exitMsg r, assumeGuarantees := false } : ChannelInteraction (exitChannel (p := p))).toRaw,
   AbstractInteraction.toAccess env
        ({ mult := -r.is_commit.result, msg := ⟨natConst 145, 1⟩, assumeGuarantees := true } : ChannelInteraction (publicValuesChannel (p := p))).toRaw,
   AbstractInteraction.toAccess env
        ({ mult := -r.is_commit_deferred.result, msg := ⟨natConst 147, 1⟩, assumeGuarantees := true } : ChannelInteraction (publicValuesChannel (p := p))).toRaw,
   AbstractInteraction.toAccess env
        ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 0, r.digest_word[0]⟩, assumeGuarantees := true } : ChannelInteraction (publicValuesChannel (p := p))).toRaw,
   AbstractInteraction.toAccess env
        ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 1, r.digest_word[1]⟩, assumeGuarantees := true } : ChannelInteraction (publicValuesChannel (p := p))).toRaw,
   AbstractInteraction.toAccess env
        ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 2, r.digest_word[2]⟩, assumeGuarantees := true } : ChannelInteraction (publicValuesChannel (p := p))).toRaw,
   AbstractInteraction.toAccess env
        ({ mult := -r.is_commit.result, msg := ⟨selectedIndex r 32 4 + 3, r.digest_word[3]⟩, assumeGuarantees := true } : ChannelInteraction (publicValuesChannel (p := p))).toRaw,
   AbstractInteraction.toAccess env
        ({ mult := -(r.is_real * r.is_commit_deferred.result), msg := ⟨selectedIndex r 72 1, reduceWord r.op_c_memory.prev_value⟩, assumeGuarantees := true } : ChannelInteraction (publicValuesChannel (p := p))).toRaw]

/-- **Chip-level faithfulness anchor — interaction half.** The native circuit's complete emitted
interaction multiset and SP1's extracted whole-table interaction multiset agree, once the row's
native-only public-value hand-off is added to the oracle side.

Five per-bus comparisons plus one shuffle. `nativeAccesses` groups by channel and the oracle's
partition groups by kind; they agree on the four SP1 instruction buses, and the syscall send is on
its own channel natively while it is the `Syscall` block on the oracle side — so one element moves
past the eight hand-off messages. Memory and Program carry the project-wide polarity flip, which is
why `negMult` appears twice on each. -/
theorem syscallInstrsChipInteractionsFaithful (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (env : Environment (ZMod p))
    (r : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ) :
    List.Perm (nativeAccesses env ((SyscallInstrsChip.main r).operations offset))
      (((Extracted.SyscallInstrsCols.interactions (syscallInstrsRustColumns env r) preprocessed
          publicValues).map Extracted.Interaction.toAccess)
        ++ syscallInstrsPublicValueAccesses env r) := by
  obtain ⟨⟨hexit, hpv⟩, hother⟩ :=
    syscallInstrsRustEmptyBlocks preprocessed publicValues (syscallInstrsRustColumns env r)
  have hrust := LookupAccessList.perm_filter_by_kind_of_sp1_with_syscall
    (((Extracted.SyscallInstrsCols.interactions (syscallInstrsRustColumns env r) preprocessed
      publicValues).map Extracted.Interaction.toAccess)) hexit hpv hother
  have hmemNeg := syscallInstrsMemoryAccesses preprocessed publicValues env r offset
  have hprogNeg := syscallInstrsProgramAccesses preprocessed publicValues env r offset
  simp only [nativeAccesses, syscallInstrsStateAccesses preprocessed publicValues env r offset,
    hmemNeg, hprogNeg, LookupAccessList.map_negMult_negMult,
    syscallInstrsUnexpectedInteractions, syscallInstrsPublicValueAccesses,
    List.map_cons, List.map_nil]
  refine List.Perm.trans ?_ (hrust.append_right _).symm
  rw [← syscallInstrsSyscallAccesses preprocessed publicValues env r]
  have hbyte := syscallInstrsByteAccesses preprocessed publicValues env r offset
  simp only [List.append_assoc]
  exact (hbyte.append
    (((List.perm_append_comm (l₁ := [_, _, _, _, _, _, _, _]) (l₂ := [_])).append_left
      _).append_left _)).append_left _

/-! ## The constructive whole-chip boundary -/

omit [Fact (2 ^ 17 < p)] in
/-- The Rust row a reconstructed native row induces is the row itself. -/
theorem syscallInstrsRustColumns_deconfigure (cols : Extracted.SyscallInstrsCols (ZMod p))
    (data : ProverData (ZMod p)) :
    syscallInstrsRustColumns (syscallInstrsEnvironment cols data)
        (varFromOffset SyscallInstrsChip.Inputs 0) = cols := by
  rw [← syscallInstrsReconfigure_eval, syscallInstrsEnvironment_eval,
    syscallInstrsReconfigure_deconfigure]

/-- **Constructive assertion agreement.** For every Rust row and prover data, the extracted
whole-table assertion list holds exactly when Clean's full constraint predicate holds on the
reconstructed physical row, together with the eight public-value conjuncts. -/
theorem syscallInstrsChipConstraintsConstructive (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (rustCols : Extracted.SyscallInstrsCols (ZMod p))
    (data : ProverData (ZMod p)) :
    List.Forall (· = 0)
        ((syscallInstrsChipOracle preprocessed publicValues).assertZeros rustCols) ↔
      (({ circuit := SyscallInstrsChip.circuit (p := p) } :
          Air.Flat.Component (ZMod p)).operations.ConstraintsHold
            (syscallInstrsEnvironment rustCols data) ∧
        PublicValueBinding rustCols publicValues) := by
  have h := syscallInstrsChipConstraintsFaithful preprocessed publicValues
    (syscallInstrsEnvironment rustCols data) (varFromOffset SyscallInstrsChip.Inputs 0)
    (size SyscallInstrsChip.Inputs)
  rw [syscallInstrsRustColumns_deconfigure] at h
  refine h.trans (and_congr_left' ?_)
  exact (constraintsHold_iff_nativeAssertZeros (SyscallInstrsChip.circuit (p := p))
    (syscallInstrsEnvironment rustCols data) SyscallInstrsChip.lookups_empty).symm

/-- **Constructive interaction agreement.** The reconstructed native row's complete emitted
interaction multiset agrees with the extracted whole-table multiset, once the row's native-only
public-value hand-off is added to the oracle side. -/
theorem syscallInstrsChipInteractionsConstructive (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) (rustCols : Extracted.SyscallInstrsCols (ZMod p))
    (data : ProverData (ZMod p)) :
    List.Perm
      (nativeAccesses (syscallInstrsEnvironment rustCols data)
        ({ circuit := SyscallInstrsChip.circuit (p := p) } : Air.Flat.Component (ZMod p)).operations)
      ((syscallInstrsChipOracle preprocessed publicValues).rustAccesses rustCols ++
        syscallInstrsPublicValueAccesses (syscallInstrsEnvironment rustCols data)
          (varFromOffset SyscallInstrsChip.Inputs 0)) := by
  have h := syscallInstrsChipInteractionsFaithful preprocessed publicValues
    (syscallInstrsEnvironment rustCols data) (varFromOffset SyscallInstrsChip.Inputs 0)
    (size SyscallInstrsChip.Inputs)
  rw [syscallInstrsRustColumns_deconfigure] at h
  rw [nativeAccesses_component_eq_rowOperations (SyscallInstrsChip.circuit (p := p)),
    Air.Flat.Component.rowOperations_mk, SyscallInstrsChip.circuit_main_eq]
  exact h

/-- **Whole-table faithfulness for `SyscallInstrs`.** The two `ChipFaithful` clauses at the
input-keyed row codec this table needs, in the factored form G5 forces.

The assertion clause carries `PublicValueBinding` and the interaction clause carries
`syscallInstrsPublicValueAccesses`, and those are the same eight facts seen from the two sides of
the arithmetization boundary: SP1 states them as row constraints against `publicValues`, and the
native row — which cannot reach the public input, because Clean's flat AIR reserves it to the
verifier — states them as messages. Nothing is dropped in either clause. What is *not* claimed is
that the messages are honoured: `Channels.publicValuesChannel` still needs an authenticated
provider. `Channels.exitChannel` already has the verifier pull and Halt-table producer, but its
terminal-row policy must be extended before active syscall rows enter the soundness theorem.
These integration obligations are disclosed in `docs/assurance.md`.

Both clauses are stated against `⟨SyscallInstrsChip.circuit⟩`, the flat component registered in the
ensemble. -/
theorem syscallInstrsChip_faithful (preprocessed : Vector (ZMod p) 0)
    (publicValues : Vector (ZMod p) 160) :
    (∀ (rustCols : Extracted.SyscallInstrsCols (ZMod p)) (data : ProverData (ZMod p)),
        List.Forall (· = 0)
            ((syscallInstrsChipOracle preprocessed publicValues).assertZeros rustCols) ↔
          (({ circuit := SyscallInstrsChip.circuit (p := p) } :
              Air.Flat.Component (ZMod p)).operations.ConstraintsHold
                (syscallInstrsEnvironment rustCols data) ∧
            PublicValueBinding rustCols publicValues)) ∧
      ∀ (rustCols : Extracted.SyscallInstrsCols (ZMod p)) (data : ProverData (ZMod p)),
        List.Forall (· = 0)
            ((syscallInstrsChipOracle preprocessed publicValues).assertZeros rustCols) →
          List.Perm
            (LookupAccessList.active
              (nativeAccesses (syscallInstrsEnvironment rustCols data)
                ({ circuit := SyscallInstrsChip.circuit (p := p) } :
                  Air.Flat.Component (ZMod p)).operations))
            (LookupAccessList.active
              ((syscallInstrsChipOracle preprocessed publicValues).rustAccesses rustCols ++
                syscallInstrsPublicValueAccesses (syscallInstrsEnvironment rustCols data)
                  (varFromOffset SyscallInstrsChip.Inputs 0))) :=
  ⟨syscallInstrsChipConstraintsConstructive preprocessed publicValues,
   fun rustCols data _ =>
     LookupAccessList.active_perm
       (syscallInstrsChipInteractionsConstructive preprocessed publicValues rustCols data)⟩

end SP1Clean.Faithful
