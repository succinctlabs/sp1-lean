# SP1 extraction and faithfulness audit

## Bottom line

The repository has a credible Rust-oracle pillar, but its evidence is uneven:

- the **flat constraint and interaction forms** are reproducible from the pinned SP1 checkout;
- the **Clean circuit forms** are compiler output transformed by a nontrivial Python normalizer, and the
  checked-in tree does not currently reproduce exactly;
- the **witness and trace vectors** are useful checked-in regressions, but the declared pinned Rust binary
  cannot regenerate a material subset of them;
- the **native-to-extracted proof anchors** are strong for operation arithmetic, but only four chips have
  full syntactic all-bus coverage.

These should be reported as four different evidence classes, not collectively as "exactly extracted and
faithful."

## Reproduction result

The updater was run against the frozen `../sp1` revision in a disposable copy of the repository, with a
fresh Cargo target directory:

```text
SP1_DIR=/Users/devontuma/Documents/SP1/sp1 \
CARGO_TARGET_DIR=/private/tmp/sp1-audit-cargo-target \
python3 update_extracted.py
```

The process exited zero despite internal failures.

### Flat forms

All 49 declared flat artifacts reproduced exactly:

- 18 operation forms;
- 6 reader forms;
- 25 chip forms.

This is the strongest part of the extraction story. It directly supports the checked-in column structs,
assertion lists, and raw interaction lists for the ordinary-instruction subset at SP1 revision
`9d249b8d4fb7d00156bf77f5d295d1dbcaaf4136`.

### Circuit forms

There are 14 checked-in files under `Extracted/Circuit`, but the updater registry contains only 13. Mul is
imported and used by the project but absent from the registry, so its checked-in circuit cannot be reproduced
by the declared all-artifacts command.

Of the 13 attempted forms, eight differed:

| Form | Difference |
| --- | --- |
| Add | `assertZero e` versus normalized `e === 0` |
| AddrAdd | `assertZero e` versus normalized `e === 0` |
| Addw | `assertZero e` versus normalized `e === 0` |
| Sub | `assertZero e` versus normalized `e === 0` |
| Subw | `assertZero e` versus normalized `e === 0` |
| U16Compare | `assertZero e` versus normalized `e === 0` |
| U16MSB | `assertZero e` versus normalized `e === 0` |
| Bitwise | Checked-in form additionally asserts `is_real * (is_real - 1) = 0` |

The first seven appear semantically equivalent API-normalization drift. Bitwise is different: the pinned
upstream operation explicitly assumes selector booleanity and emits byte lookups, while the checked-in Clean
circuit constrains booleanity itself. Strengthening a circuit can be a sound design decision, but it is not
exact extraction and can break completeness relative to upstream witnesses if left undisclosed.

The Python function `_normalize_circuit_api` also rewrites the emitted API and drops requirements, while
`render_circuit` promotes channel lists based partly on existing generated files. Therefore these files are
not raw compiler output. The normalizer is part of the trusted generation toolchain and must itself be
versioned, tested, and included in provenance claims.

### Witness vectors

Thirteen witness batteries are checked in. The pinned Rust `witness_vectors` binary implements only eight
operation dispatches: Add, Sub, LtUnsigned, IsZero, IsZeroWord, Addw, Subw, and Mul. Those eight regenerated
the same vector values; generated documentation paths differed. The following five registered families
could not be emitted:

- AddrAdd;
- Bitwise;
- IsEqualWord;
- U16Compare;
- U16MSB.

### Trace vectors

All ten checked-in whole-chip trace batteries failed regeneration. The pinned binary accepts
`--operation`, not the updater's `--chip` mode. The affected chips are Add, Sub, Addw, Subw, Bitwise, Lt,
ShiftLeft, ShiftRight, Mul, and DivRem.

`lake test` passing shows that the checked-in vectors agree with the current Lean witness closures. It does
not establish where the unsupported vectors came from or that they agree with the frozen SP1 source.

### Fail-open behavior

The updater catches exceptions independently for circuits, witnesses, and traces, prints a summary, and
still exits zero. A CI job can therefore be green after generating only a subset of the requested oracle.
This is a release-blocking provenance flaw.

## What the faithfulness theorems mean

### Assertion equivalence is generally strong

Most leaf/composed operation anchors prove an iff between the extracted assertion/interaction propositions
and the native `RawSpec`. Those proofs are valuable: they prevent the native semantic arithmetic from
silently drifting away from the upstream field equations. The subcircuit-composition discipline also means
the chip proof reuses the operation theorem rather than reimplementing its arithmetic.

The main operation exception is Mul. `mulOp_interactions_faithful` covers the byte interaction proposition,
but no theorem relates the extracted Mul assertion list to the native Mul `RawSpec`. Its completed syntactic
interaction proof is left inside a block comment because kernel checking takes roughly eight minutes. At
chip level, the reduced Mul assertion theorem does not restore this missing operation constraint equality.

DivRem has no chip faithfulness file at all.

### `Interaction.toProp` is not bus faithfulness

The extraction interpreter gives selected byte sends a range/byte-operation meaning. Every receive and all
state, memory, and program interactions reduce to `True`. Consequently a theorem of the form

```lean
List.Forall Interaction.toProp extractedInteractions ↔ NativeSpec
```

can be a strong byte-range theorem while being completely insensitive to missing, duplicated, reversed, or
mis-keyed state/memory/program traffic. This is why Addi, Lt, Jal/Jalr, UType, AluX0, and all load/store
anchors remain incomplete as SP1 bus-faithfulness evidence even when their theorem is an iff.

Bitwise, Branch, Mul, ShiftLeft, and ShiftRight are weaker still: their chip-level assertion and interaction
theorems are one-way implications into reduced specs. They intentionally discard composed portions of the
extracted constraint list.

### The four full chip anchors are normalized multiset equivalence

Add, Sub, Addw, and Subw do compare all State, Program, Memory, and Byte accesses using
`LookupAccess` lists and `List.Perm`. This is the correct direction for a multiset bus.

The result is nevertheless normalized rather than literal:

- extracted byte projection constructs a signed multiplicity independently of the raw direction field;
- program and memory blocks apply `LookupAccessList.negMult` on selected sides;
- the combined theorem concatenates per-kind blocks after those polarity conversions.

This proves equality in a chosen whole-channel balance convention. That convention may be entirely sound,
but the docs should say "polarity-normalized bus multiset equivalence," and a machine-level lemma should
prove that the normalization preserves the upstream bus-balance equation. "The emitted list is exactly
SP1's list" is too strong literally.

### Reader coverage is partial

CPUState has the best syntactic reader anchor. RType and ALUType have separate program, memory, and byte
theorems, but no combined all-bus result. IType, ITypeImmutable, and JType retain only semantic `toProp`
anchors. Since readers supply a large fraction of every chip's traffic, closing them first would make the
remaining chip proofs far cheaper through composition.

## Upstream SP1 scope

The pinned upstream `RiscvAir` enum contains 122 variants. The local 25-chip registry covers the ordinary
supervisor instruction tables, not the full proving machine. Missing upstream categories include:

- user-mode instruction variants;
- program, instruction-decode, and fetch tables;
- syscall, trap, and unconstrained-exit machinery;
- range, global-memory, page, and state-bump infrastructure;
- precompiles.

The local opcode table covers 50 of 53 declared opcodes; ECALL, EBREAK, and UNIMP are explicitly outside the
route. This is a legitimate staged scope, but it must appear in theorem names and release claims.

## Required extraction contract

A robust generator should satisfy all of the following in one command:

1. Resolve and print the active SP1 source revision and require a clean tree, or hash the patch.
2. Build the exact extractor binaries from that revision.
3. Generate every artifact into a new empty directory; never consult checked-in generated output while
   deciding the result.
4. Record a manifest containing the SP1 commit, compiler commit/options, Python generator hash, toolchain,
   and per-artifact source provenance.
5. Fail nonzero on any unsupported target, subprocess failure, missing output, duplicate registry key, or
   checked-in orphan.
6. Byte-compare all flat forms and compare normalized ASTs for circuit forms where API spelling is
   intentionally irrelevant.
7. Treat every deliberate strengthening, such as Bitwise booleanity, as a separate proved refinement layer.
8. Regenerate witness and trace vectors from the same pin and label finite batteries as tests, never proofs.

## Required faithfulness contract

Replace hand-written one-off anchors with a generated/bundled projection theorem for each artifact:

```text
Extracted asserts            ↔ native RawSpec
Extracted access multiset    ~ emitted Clean access multiset
Native semantic Spec         ↔ intended RISC-V operation
```

Here `~` should have one documented definition covering permutation and bus polarity. Once every chip uses
that theorem, retire `Interaction.toProp` as headline faithfulness evidence; retain it only as a local lemma
for byte-table semantics.
