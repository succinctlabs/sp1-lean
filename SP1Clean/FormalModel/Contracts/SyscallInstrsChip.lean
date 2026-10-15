import SP1Clean.Math.Word
import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Semantics.Specs.U16toU8Safe
import SP1Clean.Circuits.Types.IsZeroOperation
import SP1Clean.Circuits.Types.U16CompareOperation
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # System-table chip contract: the `SyscallInstrs` row

The `Inputs` row struct of SP1's ECALL table (`../sp1 crates/core/machine/src/syscall/instructions`),
the native replacement for today's single-arm `HaltChip`.

**The name carries `Instrs` because SP1's does, and the distinction matters.** Upstream has *two*
syscall types: `SyscallInstrsChip` (`syscall/instructions/mod.rs`), whose `MachineAir::name` is
`"SyscallInstrs"` and which is the ECALL *instruction* row modelled here; and `SyscallChip`
(`syscall/chip.rs`), whose name is `"SyscallCore"`/`"SyscallPrecompile"` and which is the handler
table on the far side of the syscall bus. The latter is exactly what the supported profile
excludes, and leaving `Channels.syscallChannel` unprovisioned is what forces a shard to use only
the codes this row handles inline. Dropping `Instrs` here would name this row after the table it
deliberately does *not* model.

**Why the whole table rather than one arm.** `ChipFaithful` equates two *complete* assertion systems
and interaction multisets, so an anchor between one arm and SP1's multi-arm dispatcher is not a
statable theorem. Modelling the full row is also *cheaper* than the alternative: SP1's syscall id is
little-endian `| ID | Table | unused | unused |`, and byte 1 — "the handler of this system call has
its own table" (`crates/core/executor/src/syscall_code.rs`) — is exactly the multiplicity of the
row's send on `Channels.syscallChannel`. Declaring that channel with no provider makes balance force
the byte to zero, so "the supported profile runs no precompiles" becomes a theorem instead of an
assumption, and the excluded `SyscallCore` table need not be modelled at all.

**Field order is load-bearing.** The fields below are laid out in the flat upstream column order of
`Extracted.SyscallInstrsCols` (65 cells, `CoreProfile.Table.width .syscallInstrs`), so the
faithfulness codec is a near-identity re-grouping rather than a permutation. `inputs_size` pins the
count; if a field is added, moved, or resized, that theorem is what fails.

Column map, with the upstream indices each field occupies:

| cells | field | upstream |
|---|---|---|
| 6 | `state` | `[0..5]` — `clk_high`, the two clock limbs, `pc` |
| 1 + 6 | `op_a`, `op_a_memory` | `[6]`, `[7..12]` — `t0`; its *prior* value is the syscall id |
| 1 | `op_a_0` | `[13]` — set when `op_a` is `x0`, forcing its written value to zero |
| 1 + 6 | `op_b`, `op_b_memory` | `[14]`, `[15..20]` — `a0`: exit code, or commit index |
| 1 + 6 | `op_c`, `op_c_memory` | `[21]`, `[22..27]` — `a1`: the commit digest word |
| 3 | `next_pc` | `[28..30]` |
| 1 | `is_halt` | `[31]` — already multiplied by `is_real` |
| 4 | `op_a_value` | `[32..35]` — `op_a` *after* the syscall; unlike `a0`/`a1`, which are pure reads, `t0` is genuinely written, and this is the value the read-back re-establishes |
| 4 | `syscall_id_bytes` | `[36..39]` — the id's byte split |
| 2 × 5 | the five arm selectors | `[40..49]` |
| 8 | `digest_index_bits` | `[50..57]` — one-hot over the 8 digest words |
| 4 | `digest_word` | `[58..61]` — the selected word, cached |
| 1 + 1 | `op_b_cmp`, `op_c_cmp` | `[62]`, `[63]` — valid-field-element bounds |
| 1 | `is_real` | `[64]` |

The five selectors are `IsZeroOperation` blocks on the identifier byte, at SP1's canonical codes:
`0` HALT, `3` `ENTER_UNCONSTRAINED`, `16` `COMMIT`, `26` `COMMIT_DEFERRED_PROOFS`, `240` `HINT_LEN`.
Every other identifier is a *generic* syscall, dispatched over the syscall bus. -/

namespace SP1Clean.SyscallInstrsChip

open SP1Clean.Circuits.Types

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SP1's `SyscallCode::HALT`. -/
def haltCode : ℕ := 0

/-- SP1's `SyscallCode::ENTER_UNCONSTRAINED`. -/
def enterUnconstrainedCode : ℕ := 3

/-- SP1's `SyscallCode::COMMIT`. -/
def commitCode : ℕ := 16

/-- SP1's `SyscallCode::COMMIT_DEFERRED_PROOFS`. -/
def commitDeferredCode : ℕ := 26

/-- SP1's `SyscallCode::HINT_LEN`. -/
def hintLenCode : ℕ := 240

/-- The bound both valid-field-element checks compare against: `0x7F00`, the second limb of
KoalaBear's modulus `p = 0x7F000001`. A word whose upper two limbs vanish and whose limb 1 is at
most this bound reduces to at most `p - 1`, so its single-cell reduction is injective — which is
what makes the committed exit code decode back to `a0` with no wraparound. -/
def fieldLimbBound : ℕ := 32512

/-- The `SyscallInstrs` row, grouped but in upstream column order (see the module docstring). -/
structure Inputs (F : Type) where
  state : CPUState F
  op_a : F
  op_a_memory : RegisterAccessCols F
  op_a_0 : F
  op_b : F
  op_b_memory : RegisterAccessCols F
  op_c : F
  op_c_memory : RegisterAccessCols F
  next_pc : Vector F 3
  is_halt : F
  op_a_value : Word F
  syscall_id_bytes : U16toU8Operation F
  is_enter_unconstrained : IsZeroOperation F
  is_hint_len : IsZeroOperation F
  is_halt_zero : IsZeroOperation F
  is_commit : IsZeroOperation F
  is_commit_deferred : IsZeroOperation F
  digest_index_bits : Vector F 8
  digest_word : Vector F 4
  op_b_cmp : U16CompareOperation F
  op_c_cmp : U16CompareOperation F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The row is exactly as wide as the upstream table. This is the tripwire for the whole column
map: it fails if any field above is added, removed, reordered into a different size, or if an
upstream block changes shape. -/
theorem inputs_size : size Inputs = 65 := rfl

/-- The row's recombined 24-bit low clock, the standard `clk_0_16 + clk_16_24 · 2^16` spelling. -/
def clkLow (r : Inputs (ZMod p)) : ZMod p :=
  r.state.clk_0_16 + r.state.clk_16_24 * 65536

/-- **The exit-code word is a valid field element.** SP1's halt arm pins `a0`'s upper two limbs and
bounds limb 1 against `fieldLimbBound` (`U16CompareOperation` on `[16]` gated by `[31]`, then the
two conditionals `E88`/`E91`). Stated structurally, and therefore field-generically: the numeric
consequence — that the reduction `w0 + w1 · 2^16` is below the modulus and so decodes injectively —
needs KoalaBear's actual size and is derived where it is used, not asserted here.

This is what `HaltChip` omits. Pinning limb 1 to zero, as it does, is *strictly stronger* than SP1
and costs the profile every exit code above `2^16`. -/
def ExitCodeValid (w : Word (ZMod p)) : Prop :=
  w[2] = 0 ∧ w[3] = 0 ∧
    (w[1].val < fieldLimbBound ∨ (w[1].val = fieldLimbBound ∧ w[0] = 0))

/-- Byte 0 of the syscall identifier — the code the arms dispatch on. -/
def syscallId (r : Inputs (ZMod p)) : ZMod p := r.syscall_id_bytes.low_bytes[0]

/-- Byte 1 — SP1's "this handler has its own table" flag, and the multiplicity of the row's
syscall-bus send. Balance against an unprovisioned channel forces it to zero. -/
def tableByte (r : Inputs (ZMod p)) : ZMod p :=
  (r.op_a_memory.prev_value[0] - r.syscall_id_bytes.low_bytes[0]) * (256 : ZMod p)⁻¹

/-- The row's five booleanity gates, all asserted ungated upstream so they hold on padding too. -/
def GatesBoolean (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧
  (r.is_commit.result = 0 ∨ r.is_commit.result = 1) ∧
  (r.is_commit_deferred.result = 0 ∨ r.is_commit_deferred.result = 1) ∧
  (r.is_halt = 0 ∨ r.is_halt = 1) ∧
  (tableByte r = 0 ∨ tableByte r = 1)

/-- **Arm selection.** Each `IsZeroOperation` result is the indicator of its canonical code, and
`is_halt` is the HALT indicator already multiplied by `is_real` — upstream's `[31]`. A padding row
selects nothing and dispatches nothing. -/
def SelectorsValid (r : Inputs (ZMod p)) : Prop :=
  _root_.SP1Clean.U16toU8OperationSafe.Spec
    { u16_values := r.op_a_memory.prev_value, cols := r.syscall_id_bytes, is_real := r.is_real } ∧
  (r.is_real = 1 →
    r.is_halt_zero.result = (if syscallId r = (haltCode : ℕ) then 1 else 0) ∧
    r.is_enter_unconstrained.result =
      (if syscallId r = (enterUnconstrainedCode : ℕ) then 1 else 0) ∧
    r.is_hint_len.result = (if syscallId r = (hintLenCode : ℕ) then 1 else 0) ∧
    r.is_commit.result = (if syscallId r = (commitCode : ℕ) then 1 else 0) ∧
    r.is_commit_deferred.result =
      (if syscallId r = (commitDeferredCode : ℕ) then 1 else 0)) ∧
  -- The inverse witnesses each `IsZeroOperation` needs on a non-matching code.
  (r.is_real = 1 →
    (syscallId r - (haltCode : ℕ) ≠ 0 →
      r.is_halt_zero.inverse * (syscallId r - (haltCode : ℕ)) = 1) ∧
    (syscallId r - (enterUnconstrainedCode : ℕ) ≠ 0 →
      r.is_enter_unconstrained.inverse * (syscallId r - (enterUnconstrainedCode : ℕ)) = 1) ∧
    (syscallId r - (hintLenCode : ℕ) ≠ 0 →
      r.is_hint_len.inverse * (syscallId r - (hintLenCode : ℕ)) = 1) ∧
    (syscallId r - (commitCode : ℕ) ≠ 0 →
      r.is_commit.inverse * (syscallId r - (commitCode : ℕ)) = 1) ∧
    (syscallId r - (commitDeferredCode : ℕ) ≠ 0 →
      r.is_commit_deferred.inverse * (syscallId r - (commitDeferredCode : ℕ)) = 1)) ∧
  r.is_halt = r.is_halt_zero.result * r.is_real ∧
  (r.is_real = 0 →
    tableByte r = 0 ∧ r.is_halt = 0 ∧ r.is_commit_deferred.result = 0)

/-! ## Arm contracts

Each arm of the dispatch is its own proof boundary (see `Native/Chips/SyscallInstrsChip/Arms.lean`
for why). Its `Inputs` carries only the columns it constrains, and its `Spec` states that arm's
meaning; the row's `RowContract` above is what supplies them. -/

namespace PcArm

/-- The columns the program-counter arm constrains. -/
structure Inputs (F : Type) where
  pc : Vector F 3
  next_pc : Vector F 3
  is_real : F
  is_halt : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Both gates are boolean — the row asserts this ungated, so it holds on padding too. -/
def Assumptions (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧ (r.is_halt = 0 ∨ r.is_halt = 1)

/-- `HALT` parks at `haltPc`; every other live arm advances one instruction. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  (r.is_halt = 1 → r.next_pc[0] = 1 ∧ r.next_pc[1] = 0 ∧ r.next_pc[2] = 0) ∧
  (r.is_real = 1 → r.is_halt = 0 →
    r.next_pc[0] = r.pc[0] + 4 ∧ r.next_pc[1] = r.pc[1] ∧ r.next_pc[2] = r.pc[2])

end PcArm

namespace CommitArm

/-- The columns the commit arms constrain: the one-hot digest-index bitmap, the cached digest
word, the two operands, and the two commit selectors. -/
structure Inputs (F : Type) where
  index_bits : Vector F 8
  digest_word : Vector F 4
  op_b : Word F
  op_c : Word F
  is_commit : F
  is_commit_deferred : F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The two commit selectors are boolean and mutually exclusive — a row cannot be both `COMMIT`
and `COMMIT_DEFERRED_PROOFS`, since one identifier cannot equal two codes. -/
def Assumptions (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧
  (r.is_commit = 0 ∨ r.is_commit = 1) ∧
  (r.is_commit_deferred = 0 ∨ r.is_commit_deferred = 1) ∧
  (r.is_real = 1 → r.is_commit + r.is_commit_deferred = 0 ∨
    r.is_commit + r.is_commit_deferred = 1)

/-- The bitmap's sum, one on a commit arm and zero elsewhere. -/
def bitSum (r : Inputs (ZMod p)) : ZMod p :=
  r.index_bits[0] + r.index_bits[1] + r.index_bits[2] + r.index_bits[3] +
    r.index_bits[4] + r.index_bits[5] + r.index_bits[6] + r.index_bits[7]

/-- On a commit arm the bitmap is one-hot and its set position is `a0`'s low limb, so `a0` names a
digest word index; `a1` then carries that word, packed two bytes to a limb. Off a commit arm no
bit is set. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  (∀ i : Fin 8, r.is_real = 1 → r.index_bits[i] = 0 ∨ r.index_bits[i] = 1) ∧
  (r.is_real = 1 → ∀ i : Fin 8, r.index_bits[i] = 1 → r.op_b[0] = (i.val : ℕ)) ∧
  (r.is_real = 1 → r.is_commit + r.is_commit_deferred = 1 → bitSum r = 1) ∧
  (r.is_real = 1 → r.is_commit + r.is_commit_deferred = 0 → bitSum r = 0) ∧
  (r.is_real = 1 → r.is_commit + r.is_commit_deferred = 1 →
    r.op_b[1] + r.op_b[2] + r.op_b[3] = 0) ∧
  (r.is_real = 1 → r.is_commit = 1 →
    r.op_c[0] = r.digest_word[0] + r.digest_word[1] * 256 ∧
      r.op_c[1] = r.digest_word[2] + r.digest_word[3] * 256 ∧
      r.op_c[2] = 0 ∧ r.op_c[3] = 0)

end CommitArm

namespace WriteArm

/-- The columns the `t0` write arms constrain. -/
structure Inputs (F : Type) where
  op_a_prev : Word F
  op_a_value : Word F
  op_a_0 : F
  is_enter_unconstrained : F
  is_hint_len : F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- `ENTER_UNCONSTRAINED` and `HINT_LEN` are boolean and mutually exclusive, and the `x0` flag is
boolean (the Program fetch's `RowSpec` carries it). -/
def Assumptions (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧
  (r.op_a_0 = 0 ∨ r.op_a_0 = 1) ∧
  (r.is_real = 1 → r.is_enter_unconstrained = 0 ∨ r.is_enter_unconstrained = 1) ∧
  (r.is_real = 1 → r.is_enter_unconstrained + r.is_hint_len = 0 ∨
    r.is_enter_unconstrained + r.is_hint_len = 1)

/-- `ENTER_UNCONSTRAINED` zeroes `t0`; `HINT_LEN` leaves it free — the oracled hint length, which
is why no arm determines it there; every other arm leaves it unchanged. A syscall row never
targets `x0`, so the x0 zeroing is vacuous on a live row but still asserted. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 1 → r.op_a_0 = 0) ∧
  (r.op_a_0 = 1 → ∀ i : Fin 4, r.op_a_value[i] = 0) ∧
  (r.is_real = 1 → r.is_enter_unconstrained = 1 → ∀ i : Fin 4, r.op_a_value[i] = 0) ∧
  (r.is_real = 1 → r.is_enter_unconstrained + r.is_hint_len = 0 →
    ∀ i : Fin 4, r.op_a_value[i] = r.op_a_prev[i])

end WriteArm

namespace FieldBoundArm

/-- The columns one valid-field-element check constrains: the word being bounded, the comparison
bit, and the gate. The row uses this twice — on `a0` for `HALT` and on `a1` for
`COMMIT_DEFERRED_PROOFS` — which is the reason it is its own assertion. -/
structure Inputs (F : Type) where
  word : Word F
  bit : F
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The gate is boolean, and on a live gate the word's second limb is a `u16` — it is read from a
register, so the Memory bus already carries that. -/
def Assumptions (r : Inputs (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧ (r.is_real = 1 → r.word[1].val < 2 ^ 16)

/-- On a live gate the word is a valid field element: `ExitCodeValid`, and the comparison bit is
the strict-less-than indicator that decides which branch of it holds. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  (r.bit = 0 ∨ r.bit = 1) ∧
  (r.is_real = 1 →
    r.bit = (if r.word[1].val < fieldLimbBound then 1 else 0) ∧ ExitCodeValid r.word)

end FieldBoundArm

namespace DispatchArm

/-- The columns the generic-dispatch check constrains. -/
structure Inputs (F : Type) where
  op_b : Word F
  op_c : Word F
  table_byte : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The identifier's table byte is boolean. -/
def Assumptions (r : Inputs (ZMod p)) : Prop :=
  r.table_byte = 0 ∨ r.table_byte = 1

/-- A syscall dispatched over the bus carries only three operand limbs, so the fourth vanishes. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  r.table_byte = 1 → r.op_b[3] = 0 ∧ r.op_c[3] = 0

end DispatchArm


/-! ## Projections into the arms

Each arm constrains a slice of the row. These name that slice once, so the row's contract and its
`main` agree on it by construction. -/

/-- The program-counter arm's slice. -/
def toPcArm (r : Inputs (ZMod p)) : PcArm.Inputs (ZMod p) :=
  ⟨r.state.pc, r.next_pc, r.is_real, r.is_halt⟩

/-- The `t0` write arms' slice. -/
def toWriteArm (r : Inputs (ZMod p)) : WriteArm.Inputs (ZMod p) :=
  ⟨r.op_a_memory.prev_value, r.op_a_value, r.op_a_0,
   r.is_enter_unconstrained.result, r.is_hint_len.result, r.is_real⟩

/-- The generic-dispatch check's slice. -/
def toDispatchArm (r : Inputs (ZMod p)) : DispatchArm.Inputs (ZMod p) :=
  ⟨r.op_b_memory.prev_value, r.op_c_memory.prev_value, tableByte r⟩

/-- The `HALT` exit-code bound's slice: `a0`, gated on `is_halt`. -/
def toFieldBoundB (r : Inputs (ZMod p)) : FieldBoundArm.Inputs (ZMod p) :=
  ⟨r.op_b_memory.prev_value, r.op_b_cmp.bit, r.is_halt⟩

/-- The `COMMIT_DEFERRED_PROOFS` bound's slice: `a1`, gated on that selector. -/
def toFieldBoundC (r : Inputs (ZMod p)) : FieldBoundArm.Inputs (ZMod p) :=
  ⟨r.op_c_memory.prev_value, r.op_c_cmp.bit, r.is_commit_deferred.result⟩

/-- The commit arms' slice. -/
def toCommitArm (r : Inputs (ZMod p)) : CommitArm.Inputs (ZMod p) :=
  ⟨r.digest_index_bits, r.digest_word, r.op_b_memory.prev_value, r.op_c_memory.prev_value,
   r.is_commit.result, r.is_commit_deferred.result, r.is_real⟩

/-- **The facts the row's pulls carry.** A consumer of the Program and Memory buses derives these
from the provider; the prover, running completeness in the other direction, must supply them. They
are ordinary well-formedness of the fetched instruction and of the three prior register records. -/
def PulledFacts (r : Inputs (ZMod p)) : Prop :=
  r.is_real = 1 →
    r.op_a.val < 32 ∧
    r.state.pc[0].val < 2 ^ 16 ∧ r.state.pc[1].val < 2 ^ 16 ∧ r.state.pc[2].val < 2 ^ 16 ∧
    (r.op_a_0 = 0 ∨ r.op_a_0 = 1) ∧
    Word.isU64 r.op_a_memory.prev_value ∧
    r.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    Word.isU64 r.op_b_memory.prev_value ∧
    r.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    Word.isU64 r.op_c_memory.prev_value ∧
    r.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    -- The written `t0` word, which the row range-checks itself: on the `HINT_LEN` arm no
    -- constraint determines it, so this is the only thing making the read-back pushable.
    Word.isU64 r.op_a_value

/-- **What an honest prover must supply**, and the row's full arm-by-arm contract: the gates, the
reader blocks, arm selection, and one predicate per arm family. Every arm SP1 dispatches inline
appears here, so an arm without a contract is a missing conjunct rather than a silent gap.

This is the chip's `ProverAssumptions` — the completeness precondition — and it is deliberately
*wider* than `Spec`, the soundness conclusion. Clean keeps the two apart on purpose: soundness
reports what a consumer may rely on, while completeness must reconstruct every constraint the row
emits, including the arm bookkeeping no consumer reads. `rowContract_toSpec` records that the
former follows from the latter. -/
def RowContract (r : Inputs (ZMod p)) : Prop :=
  GatesBoolean r ∧
  Readers.CPUState.Spec
    { cols := r.state, next_pc := r.next_pc, clk_inc := 264, is_real := r.is_real } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_a_memory, is_real := r.is_real, clk_target := clkLow r + 4 } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_b_memory, is_real := r.is_real, clk_target := clkLow r + 3 } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_c_memory, is_real := r.is_real, clk_target := clkLow r + 2 } ∧
  SelectorsValid r ∧
  WriteArm.Assumptions (toWriteArm r) ∧ WriteArm.Spec (toWriteArm r) ∧
  PcArm.Assumptions (toPcArm r) ∧ PcArm.Spec (toPcArm r) ∧
  DispatchArm.Assumptions (toDispatchArm r) ∧ DispatchArm.Spec (toDispatchArm r) ∧
  FieldBoundArm.Assumptions (toFieldBoundB r) ∧ FieldBoundArm.Spec (toFieldBoundB r) ∧
  FieldBoundArm.Assumptions (toFieldBoundC r) ∧ FieldBoundArm.Spec (toFieldBoundC r) ∧
  CommitArm.Assumptions (toCommitArm r) ∧ CommitArm.Spec (toCommitArm r) ∧
  PulledFacts r ∧
  (r.is_commit.result = 1 → ∀ i : Fin 4, r.digest_word[i].val < 256)

/-- **What a consumer may rely on.** The gates, the reader blocks at the syscall edge
(`clk_inc = 264`, access clocks `+4`/`+3`/`+2`), and each arm's own meaning. Assembling it from the
arm `Spec`s rather than restating them is what keeps the row and its decomposition from drifting. -/
def Spec (r : Inputs (ZMod p)) : Prop :=
  GatesBoolean r ∧
  Readers.CPUState.Spec
    { cols := r.state, next_pc := r.next_pc, clk_inc := 264, is_real := r.is_real } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_a_memory, is_real := r.is_real, clk_target := clkLow r + 4 } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_b_memory, is_real := r.is_real, clk_target := clkLow r + 3 } ∧
  Readers.RegisterAccessCols.Spec
    { cols := r.op_c_memory, is_real := r.is_real, clk_target := clkLow r + 2 } ∧
  -- `op_a_0`'s booleanity reaches this row over the Program bus, which is gated; SP1 nonetheless
  -- asserts the x0 rule ungated, so on a padding row the prover must choose `op_a_0 = 0`. The
  -- write arm's meaning is therefore reported under exactly that hypothesis.
  ((r.op_a_0 = 0 ∨ r.op_a_0 = 1) → WriteArm.Spec (toWriteArm r)) ∧
  PcArm.Spec (toPcArm r) ∧
  DispatchArm.Spec (toDispatchArm r) ∧
  FieldBoundArm.Spec (toFieldBoundB r) ∧
  FieldBoundArm.Spec (toFieldBoundC r) ∧
  CommitArm.Spec (toCommitArm r) ∧
  -- ⚠ **Load-bearing, and the reason it is here rather than only in `RowContract`.** Every arm
  -- `Spec` above is phrased over the `IsZero` selectors, while every semantic law is phrased over
  -- the *event's* natural identifier. `SelectorsValid` is the only thing tying a selector to
  -- `syscallId`, so without it in the soundness conclusion no per-arm theorem is reachable from
  -- constraints — the row's meaning would stop at the circuit boundary.
  SelectorsValid r

omit [Fact (2 ^ 17 < p)] in
/-- `SelectorsValid` is `Spec`'s final conjunct.  Project it by name: reaching it positionally means
an eleven-deep chain of `.2`s, which silently re-points to a different conjunct the moment anyone
inserts one — and this is the conjunct every per-arm semantic theorem turns on. -/
theorem Spec.selectorsValid {r : Inputs (ZMod p)} (h : Spec r) : SelectorsValid r :=
  h.2.2.2.2.2.2.2.2.2.2.2

omit [Fact (2 ^ 17 < p)] in
/-- The soundness conclusion follows from the prover's obligation, so the two never drift apart. -/
theorem rowContract_toSpec {r : Inputs (ZMod p)} (h : RowContract r) : Spec r :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    (fun _ => h.2.2.2.2.2.2.2.1), h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.1⟩


end SP1Clean.SyscallInstrsChip
