---
name: is_trusted removal baseline commit
description: Commit e686807 is the ground truth for what changed when is_trusted was dropped — old indices, removed columns, opcode updates.
type: reference
originSessionId: 46ad662a-b54b-497b-a0ef-b07390243b4b
---
Commit `e686807` ("Updated extraction without is_trusted and some opcode changes") is the baseline for any work related to the is_trusted field removal. When reconstructing old indices or understanding what shifted:

- `git show e686807^:SP1Chips/<Chip>/Constraints.lean` — the old generated constraint (still has `is_trusted := Main[k]` fields, tells you which column was removed)
- `git show e686807 -- SP1Chips/<Chip>/Constraints.lean` — the diff showing exactly which indices shifted
- `git show e686807 -- SP1Operations/Reader/<ReaderType>.lean` — shows the `allHold_constraints_iff*` lemmas losing their `cols.is_trusted = 1` conjunct

The commit touches 42 files. Readers affected: `RTypeReader`, `ITypeReader`, `ITypeReaderImmutable`, `ALUTypeReader` — all have their `is_trusted` field removed from the cols record.

Some chips also got opcode number changes in the same commit (e.g. Jal's `.send (.program ...)` opcode went from 33 to 46). Check the diff before assuming index shifts are the only change.
