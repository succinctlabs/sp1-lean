# U16 Composition Proof Guide for SP1-Lean

This guide helps future Claude Code instances complete U16 composition proofs in the SP1-Lean framework.

## Overview

U16 composition proofs verify that all field elements used in SP1 chip constraints respect 16-bit bounds (< 65536) when `is_real` is true. These proofs are crucial for ensuring the soundness of the zero-knowledge virtual machine implementation.

## Key Concepts

### 1. U16CompProp Definition
```lean
def SP1ConstraintList.U16CompProp (xs : SP1ConstraintList) : Prop :=
  List.Forall SP1Constraint.toU16CompProp xs
```

The `toU16CompProp` function extracts bounds requirements from constraints:
- For memory receive operations: proves limbs and addresses are < 65536
- For program send operations: proves PC components are bounded appropriately

### 2. Proof Structure Pattern

Most U16 composition proofs follow this structure:

```lean
def u16_composition : (constraints Main).U16CompProp := by
  -- 1. Expand definitions
  simp [SP1Constraint.toU16CompProp, constraints, List.Forall, 
        AddOperation.constraints, CPUState.constraints, ITypeReader.constraints]
  
  -- 2. Decompose constraints hypothesis
  simp [constraints] at cstrs
  obtain ⟨op_cstrs, cpu_cstrs, reader_cstrs, rest⟩ := cstrs
  
  -- 3. Prove each conjunct
  refine ⟨?_, ?_, ?_⟩
```

## Step-by-Step Approach

### Step 1: Initial Setup
Always start with:
```lean
simp [SP1Constraint.toU16CompProp, constraints, List.Forall, ...]
```
This expands the goal into explicit bounds requirements.

### Step 2: Understand the Goal
Use the `lean_goal` tool to see the expanded goal. It typically has the form:
```
(¬Main[is_real_idx] = 0 → bounds₁) ∧ 
(¬Main[is_real_idx] = 0 → bounds₂) ∧ ...
```

### Step 3: Decompose Constraints
```lean
simp [constraints] at cstrs
obtain ⟨component1_cstrs, component2_cstrs, ...⟩ := cstrs
```

### Step 4: Prove Each Component
For each conjunct in the goal:
1. Introduce the `is_real` hypothesis: `intro h_is_real`
2. Expand relevant constraints: `simp [ComponentName.constraints, SP1Constraint.toProp, h_is_real, ...] at component_cstrs`
3. Extract facts using `extract_from_and`
4. Apply appropriate proof tactics

## Common Proof Patterns

### Pattern 1: PC Bounds (Program Counter)
```lean
· intro h_is_real
  simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble, Nat.beq] at reader_cstrs
  refine ⟨?_, by extract_from_and reader_cstrs, by extract_from_and reader_cstrs⟩
  -- Prove PC + 4 ≤ 65536
  have h_pc_nat_mul4 : Main[pc_idx].val % 4 = 0 := by
    have h_pc_mul4 : Main[pc_idx] % 4 = 0 := by extract_from_and reader_cstrs
    have : (Main[pc_idx] % 4).val = Main[pc_idx].val % 4 := Fin.mod_val Main[pc_idx] 4
    rw [h_pc_mul4] at this
    simp at this
    exact this.symm
  have h_pc_nat_bound : Main[pc_idx].val < 65536 := by extract_from_and reader_cstrs
  have h_no_overflow : Main[pc_idx].val + 4 < BB := by
    calc Main[pc_idx].val + 4 < 65536 + 4 := by omega
    _ = 65540 := by norm_num
    _ < BB := by norm_num
  rw [Fin.le_iff_val_le_val]
  rw [Fin.val_add_eq_of_add_lt h_no_overflow]
  omega
```

### Pattern 2: Output Bounds
```lean
· intro h_is_real
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ...] at add_op_cstrs
  refine ⟨⟨by aesop, by aesop, by aesop, by aesop⟩, ?_⟩
  -- For register bounds
  simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, ...] at reader_cstrs
  calc 
    Main[reg_idx] < 32 := by extract_from_and reader_cstrs
    _             < 65536 := by trivial
```

### Pattern 3: Word Bounds (4-element vectors)
```lean
· intro h_is_real
  simp [ITypeReader.constraints, SP1Constraint.toProp, h_is_real, ...] at reader_cstrs
  have h_is_u64 : Word.isU64 #v[Main[a], Main[b], Main[c], Main[d]] := by
    extract_from_and reader_cstrs
  refine ⟨⟨h_is_u64 0, h_is_u64 1, h_is_u64 2, h_is_u64 3⟩, ?_⟩
  extract_from_and reader_cstrs
```

## Key Tactics and Lemmas

### Essential Tactics
- `simp`: Simplifies definitions and unfolds constraints
- `extract_from_and`: Custom tactic to extract facts from nested conjunctions
- `aesop`: Automated proof search for simple goals
- `omega`: Linear arithmetic solver
- `calc`: Structured inequality proofs
- `trivial`: Solves simple goals like `32 < 65536`

### Important Lemmas
- `Fin.mod_val`: Relates Fin modulo to Nat modulo
- `Fin.le_iff_val_le_val`: Converts Fin inequalities to Nat
- `Fin.val_add_eq_of_add_lt`: Addition in Fin when no overflow
- `Word.isU64`: Proves all components of a word are < 65536

## Debugging Tips

1. **Use lean_goal frequently**: Check the goal after each `simp` to understand what needs to be proven
2. **Check diagnostic messages**: Use `lean_diagnostic_messages` to catch type errors early
3. **Examine constraint structure**: Use `Read` tool to understand the constraint definitions
4. **Follow existing examples**: Look at completed proofs (e.g., Add/U16Composition.lean) as templates
5. **Set maxHeartbeats**: Use `set_option maxHeartbeats 400000` for complex proofs

## Common Pitfalls

1. **Wrong index assumptions**: Main vector indices vary between chips - always check the constraints file
2. **Missing imports**: Ensure all necessary tactics and definitions are imported
3. **Incomplete simplification**: Some definitions need explicit unfolding with `simp`
4. **Arithmetic overflow**: Always prove no overflow before using Fin arithmetic lemmas

## Example Chips and Their Patterns

- **Add/Sub chips**: Use RTypeReader, have 33 Main elements
- **Addi chip**: Uses ITypeReader, has 30 Main elements, includes immediate values
- **And/Or/Xor chips**: Similar to Add but with bitwise operations
- **Jalr chip**: More complex PC manipulation, requires careful overflow checking

## Workflow Summary

1. Read the constraints file to understand the chip structure
2. Start with `simp` to expand all definitions
3. Use `lean_goal` to see the proof obligations
4. Decompose the constraints hypothesis
5. Prove each conjunct using the appropriate pattern
6. Use `extract_from_and` liberally to extract facts
7. Build and verify with `lake build`