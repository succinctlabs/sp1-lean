# Claim and artifact matrix

This matrix inventories the project's verification chain at the audited revision. It deliberately does not
use a single "faithful" checkbox.

## Legend

- **S/C**: native Clean circuit soundness and completeness proof.
- **Semantic iff**: the extracted assertions plus `Interaction.toProp` are equivalent to a native spec.
  This is useful for arithmetic, but `toProp` maps receive/state/memory/program interactions to `True`.
- **Reduced →**: a one-way chip theorem over a reduced assertion/interaction spec; composed operation
  constraints or non-byte buses can be discarded.
- **Syntactic normalized**: emitted Clean `LookupAccess` lists are related to the extracted list, modulo
  permutation and explicit per-bus polarity normalization. It is stronger than `toProp`, but not literal
  raw-direction equality.
- **Advance ✓\***: a native Sail-facing transition relation and bridge exist, but dispatch still requires
  external decode/readiness/specification hypotheses.
- **Trace test**: a finite, compiler-trusting `native_decide` regression anchor, not a proof.

## Chip layer: all 25 registered ordinary-instruction chips

| Chip | S/C | Sail bridge | Assertion / semantic anchor | Interaction anchor | Trace test | Audit disposition |
| --- | --- | --- | --- | --- | --- | --- |
| Add | ✓ / ✓ | Advance ✓\* | Semantic iff | Syntactic normalized, all 4 buses | ✓ | Strongest template |
| Addi | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Bus shape open |
| Addw | ✓ / ✓ | Advance ✓\* | Semantic iff | Syntactic normalized, all 4 buses | ✓ | Strongest template |
| Sub | ✓ / ✓ | Advance ✓\* | Semantic iff | Syntactic normalized, all 4 buses | ✓ | Strongest template |
| Subw | ✓ / ✓ | Advance ✓\* | Semantic iff | Syntactic normalized, all 4 buses | ✓ | Strongest template |
| Bitwise | ✓ / ✓ | Advance ✓\* | Reduced → | Reduced `toProp` → | ✓ | Circuit extraction drift; no full bus anchor |
| Lt | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | ✓ | Bus shape open |
| ShiftLeft | ✓ / ✓ | Advance ✓\* | Reduced → | Reduced `toProp` → | ✓ | No full composed/bus anchor |
| ShiftRight | ✓ / ✓ | Advance ✓\* | Reduced → | Reduced `toProp` → | ✓ | No full composed/bus anchor |
| Jal | ✓ / ✓ | Advance ✓\* | Assertions + semantic iff | `toProp` only | — | Bus shape open |
| Jalr | ✓ / ✓ | Advance ✓\* | Assertions + semantic iff | `toProp` only | — | Bus shape open |
| Branch | ✓ / ✓ | Advance ✓\* | Reduced → | Reduced `toProp` → | — | No full composed/bus anchor |
| UType | ✓ / ✓ | Advance ✓\* | Assertions + semantic iff | `toProp` only | — | Bus shape open |
| LoadByte | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| LoadHalf | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| LoadWord | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| LoadDouble | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| LoadX0 | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| StoreByte | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Readiness owns an out-of-row ROM fact |
| StoreHalf | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| StoreWord | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| StoreDouble | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | Memory/state/program list shape open |
| Mul | ✓ / **sorry** | Advance ✓\* | Reduced → | Reduced `toProp` → | ✓ | Completeness hole; operation assertion anchor absent |
| DivRem | **stop** / **stop** | Advance ✓\* | None | None | ✓ | Direct proof holes and no SP1 faithfulness anchor |
| AluX0 | ✓ / ✓ | Advance ✓\* | Semantic iff | `toProp` only | — | 29-way readiness seam; bus shape open |

All 25 have an extracted flat Rust form, a `GeneralFormalCircuit`, a registry entry, and an `advance`
relation. That is good architectural coverage. It should not be described as 25 fully proved faithful SP1
chips until the bold and interaction columns are closed.

## Operation layer

| Operation | Native S/C | Extracted assertion relation | Syntactic interaction relation | Circuit form | Witness test at pin |
| --- | --- | --- | --- | --- | --- |
| Add | ✓ | Iff | ✓ | Registered; API-normalization diff | Reproduced |
| Sub | ✓ | Iff | ✓ | Registered; API-normalization diff | Reproduced |
| AddrAdd | ✓ | Iff | ✓ | Registered; API-normalization diff | Unsupported emitter |
| Addw | ✓ | Iff | ✓ | Registered; API-normalization diff | Reproduced |
| Subw | ✓ | Iff | ✓ | Registered; API-normalization diff | Reproduced |
| Bitwise | ✓ | Iff | ✓ | Registered; substantive extra gate | Unsupported emitter |
| IsEqualWord | ✓ | Iff | ✓ | Registered; exact | Unsupported emitter |
| IsZero | ✓ | Iff | ✓ | Registered; exact | Reproduced |
| IsZeroWord | ✓ | Iff | ✓ | Registered; exact | Reproduced |
| LtUnsigned | ✓ | Iff | ✓ | Registered; exact | Reproduced |
| LtSigned | ✓ | Iff | Through composed subanchors only | Registered; exact | No battery |
| Mul | ✓ | **No assertion/RawSpec anchor** | Semantic only; syntactic proof commented out | **Checked in but unregistered** | Reproduced |
| U16Compare | ✓ | Iff | ✓ | Registered; API-normalization diff | Unsupported emitter |
| U16MSB | ✓ | Iff | ✓ | Registered; API-normalization diff | Unsupported emitter |
| Address | Native flat gadget | Iff | `toProp` within combined theorem | No circuit form | No battery |
| BitwiseU16 | Native flat gadget | Iff | `toProp` within combined theorem | No circuit form | No battery |
| U16toU8Safe | Native flat gadget | Iff | ✓ | No circuit form | No battery |
| U16toU8Unsafe | Native flat gadget | Iff | ✓ | No circuit form | No battery |

The 24 extracted operation/reader flat forms and 25 chip flat forms all reproduced byte-for-byte. Circuit
forms are a distinct artifact class: there are 14 checked-in forms, but only 13 registry entries.

## Reader layer

| Reader | Extracted flat form | Native implementation | Semantic faithfulness | Syntactic interaction coverage |
| --- | --- | --- | --- | --- |
| CPUState | Reproduced | ✓ | Iff | Combined/state + byte anchors |
| RType | Reproduced | ✓ | Iff | Memory, program, byte; no combined all-bus theorem |
| ALUType | Reproduced | ✓ | Iff | Memory, program, byte; no combined all-bus theorem |
| IType | Reproduced | ✓ | Iff | None |
| ITypeImmutable | Reproduced | ✓ | Iff | None |
| JType | Reproduced | ✓ | Iff | None |

`ALUTypeReaderImmutable` and several register-access helpers are native composition infrastructure without
matching top-level extracted reader artifacts. That is not intrinsically a problem, but the distinction
should be explicit in generated inventories.

## Whole-machine claims

| Declaration / layer | What Lean currently establishes | What it does not establish |
| --- | --- | --- |
| `sp1Ensemble` | A Clean ensemble of the registered tables and boundaries | Public program binding or upstream SP1 public-value equivalence |
| `sp1_machine_soundness` | The ensemble spec, downstream of a sorry-backed witness decode | A Sail execution; the spec is only existence of a balance trail |
| `GatedExecution` | A path through balanced `StateKey` edges | Use of every chip row, chip semantics, program fetch, memory correctness, or Sail stepping |
| `chipRows_advance_sound` | Row-wise `advance` under five families of supplied hypotheses | Derivation of those hypotheses from the ensemble |
| `targetObligations_via_advance` | Conditional conversion from `advance` to target obligations | Decode/readiness/boundary/halt discharge |
| `sp1_target_execution` | A real Sail-chain walk induction from target obligations | Production of the obligations from current Clean soundness |
| `sp1_target_soundness` | The target result under arbitrary obligation and entry hypotheses | End-to-end verification from an SP1 proof/public statement |
| `sp1_partial_completeness` | Opcode routing membership | A circuit witness, accepted chip row, trace, or VM proof |
| `InstructionTrace.Emits` | Route, `is_real`, and opcode fields | PC, operands, immediate, result, witness columns, and emitted bus messages |

## Upstream scope boundary

The local registry covers 25 supervisor ordinary-instruction chips and routes 50 of 53 local opcodes.
ECALL, EBREAK, and UNIMP are not routed. The pinned upstream `RiscvAir` enum contains 122 variants: the
remaining variants include user-mode copies, fetch/decode/program tables, syscalls and traps, byte/range and
global-memory infrastructure, page/state machinery, StateBump, and precompiles. The honest current scope is
therefore "the ordinary supervisor instruction-chip subset," not the complete SP1 zkVM.

The row-level CSV companion is [artifact-matrix.csv](artifact-matrix.csv).
