//! Compare Clean's generated instruction code directly with the released SP1 Rust AIR.
//! These are component tests: global provider balance and lowering correctness are separate claims.

extern crate alloc;

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as NativeField;
use slop_air::{Air, BaseAir};
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::{dense::RowMajorMatrix, Matrix};
use sp1_core_executor::{
    events::{
        AluEvent, BranchEvent, JumpEvent, MemInstrEvent, MemoryReadRecord, MemoryRecordEnum,
        MemoryWriteRecord, UTypeEvent,
    },
    get_quotient_and_remainder, ALUTypeRecord, ExecutionRecord, ITypeRecord, JTypeRecord, Opcode,
    RTypeRecord,
};
use sp1_core_machine::{
    alu::{
        add_sub::{
            add::AddChip,
            addi::{AddiChip, AddiCols},
            addw::{AddwChip, AddwCols},
            sub::{SubChip, SubCols},
            subw::{SubwChip, SubwCols},
        },
        alu_x0::{AluX0Chip, AluX0Cols},
        bitwise::{BitwiseChip, BitwiseCols},
        divrem::{DivRemChip, DivRemCols},
        lt::{LtChip, LtCols},
        mul::{MulChip, MulCols},
        sll::{ShiftLeftChip, ShiftLeftCols},
        sr::{ShiftRightChip, ShiftRightCols},
    },
    control_flow::{BranchChip, BranchColumns, JalChip, JalColumns, JalrChip, JalrColumns},
    memory::{
        load::{
            load_byte::{LoadByteChip, LoadByteColumns},
            load_double::{LoadDoubleChip, LoadDoubleColumns},
            load_half::{LoadHalfChip, LoadHalfColumns},
            load_word::{LoadWordChip, LoadWordColumns},
            load_x0::{LoadX0Chip, LoadX0Columns},
        },
        store::{
            store_byte::{StoreByteChip, StoreByteColumns},
            store_double::{StoreDoubleChip, StoreDoubleColumns},
            store_half::{StoreHalfChip, StoreHalfColumns},
            store_word::{StoreWordChip, StoreWordColumns},
        },
    },
    utype::{UTypeChip, UTypeColumns},
    SupervisorMode,
};
use sp1_hypercube::air::{MachineAir, SP1_PROOF_NUM_PV_ELTS};
use sp1_primitives::SP1Field;
use std::mem::offset_of;

// Clean emits shared helpers that some individual components do not use.
macro_rules! generated_instruction {
    ($module:ident, $file:literal, $program:ident, $air:ident) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
        use $module::{$air, $program};
    };
}
generated_instruction!(
    generated_add,
    "add_instruction.rs",
    AddInstruction,
    AddInstructionAirSpec
);
generated_instruction!(
    generated_addi,
    "addi_instruction.rs",
    AddiInstruction,
    AddiInstructionAirSpec
);
generated_instruction!(
    generated_addw,
    "addw_instruction.rs",
    AddwInstruction,
    AddwInstructionAirSpec
);
generated_instruction!(
    generated_sub,
    "sub_instruction.rs",
    SubInstruction,
    SubInstructionAirSpec
);
generated_instruction!(
    generated_subw,
    "subw_instruction.rs",
    SubwInstruction,
    SubwInstructionAirSpec
);
generated_instruction!(
    generated_bitwise,
    "bitwise_instruction.rs",
    BitwiseInstruction,
    BitwiseInstructionAirSpec
);
generated_instruction!(
    generated_lt,
    "lt_instruction.rs",
    LtInstruction,
    LtInstructionAirSpec
);
generated_instruction!(
    generated_shift_left,
    "shift_left_instruction.rs",
    ShiftLeftInstruction,
    ShiftLeftInstructionAirSpec
);
generated_instruction!(
    generated_shift_right,
    "shift_right_instruction.rs",
    ShiftRightInstruction,
    ShiftRightInstructionAirSpec
);
generated_instruction!(
    generated_jal,
    "jal_instruction.rs",
    JalInstruction,
    JalInstructionAirSpec
);
generated_instruction!(
    generated_jalr,
    "jalr_instruction.rs",
    JalrInstruction,
    JalrInstructionAirSpec
);
generated_instruction!(
    generated_branch,
    "branch_instruction.rs",
    BranchInstruction,
    BranchInstructionAirSpec
);
generated_instruction!(
    generated_u_type,
    "u_type_instruction.rs",
    UTypeInstruction,
    UTypeInstructionAirSpec
);
generated_instruction!(
    generated_load_byte,
    "load_byte_instruction.rs",
    LoadByteInstruction,
    LoadByteInstructionAirSpec
);
generated_instruction!(
    generated_load_half,
    "load_half_instruction.rs",
    LoadHalfInstruction,
    LoadHalfInstructionAirSpec
);
generated_instruction!(
    generated_load_word,
    "load_word_instruction.rs",
    LoadWordInstruction,
    LoadWordInstructionAirSpec
);
generated_instruction!(
    generated_load_double,
    "load_double_instruction.rs",
    LoadDoubleInstruction,
    LoadDoubleInstructionAirSpec
);
generated_instruction!(
    generated_load_x0,
    "load_x0_instruction.rs",
    LoadX0Instruction,
    LoadX0InstructionAirSpec
);
generated_instruction!(
    generated_store_byte,
    "store_byte_instruction.rs",
    StoreByteInstruction,
    StoreByteInstructionAirSpec
);
generated_instruction!(
    generated_store_half,
    "store_half_instruction.rs",
    StoreHalfInstruction,
    StoreHalfInstructionAirSpec
);
generated_instruction!(
    generated_store_word,
    "store_word_instruction.rs",
    StoreWordInstruction,
    StoreWordInstructionAirSpec
);
generated_instruction!(
    generated_store_double,
    "store_double_instruction.rs",
    StoreDoubleInstruction,
    StoreDoubleInstructionAirSpec
);
generated_instruction!(
    generated_mul,
    "mul_instruction.rs",
    MulInstruction,
    MulInstructionAirSpec
);
generated_instruction!(
    generated_div_rem,
    "div_rem_instruction.rs",
    DivRemInstruction,
    DivRemInstructionAirSpec
);
generated_instruction!(
    generated_alu_x0,
    "alu_x0_instruction.rs",
    AluX0Instruction,
    AluX0InstructionAirSpec
);

#[path = "support/export.rs"]
mod export_support;
use export_support::{Ledger, NativeEvaluation, RowWitness, Sp1Evaluation};

fn r_type_event(index: usize, opcode: Opcode, a: u64, b: u64, c: u64) -> (AluEvent, RTypeRecord) {
    let clk = 9 + 8 * index as u64;
    let read = |value, offset| {
        MemoryRecordEnum::Read(MemoryReadRecord {
            value,
            timestamp: clk + offset,
            prev_timestamp: clk - 8,
            prev_page_prot_record: None,
        })
    };
    (
        AluEvent::new(clk, 4096 + 4 * index as u64, opcode, a, b, c, false),
        RTypeRecord {
            op_a: 5,
            op_b: 6,
            op_c: 7,
            is_untrusted: false,
            a: MemoryRecordEnum::Write(MemoryWriteRecord {
                prev_timestamp: clk - 8,
                prev_page_prot_record: None,
                prev_value: 0,
                timestamp: clk + 4,
                value: a,
            }),
            b: read(b, 3),
            c: read(c, 2),
        },
    )
}

/// Register and immediate ALU instructions share SP1's reader record layout.
fn alu_type_event(
    index: usize,
    opcode: Opcode,
    a: u64,
    b: u64,
    c: u64,
    immediate: bool,
) -> (AluEvent, ALUTypeRecord) {
    let (event, registers) = r_type_event(index, opcode, a, b, c);
    (
        event,
        ALUTypeRecord {
            op_a: registers.op_a,
            a: registers.a,
            op_b: registers.op_b as u64,
            b: registers.b,
            op_c: if immediate { c } else { registers.op_c as u64 },
            c: if immediate { None } else { Some(registers.c) },
            is_imm: immediate,
            is_untrusted: false,
        },
    )
}

fn add_trace() -> RowMajorMatrix<SP1Field> {
    let values = [
        0,
        1,
        65535,
        65536,
        u32::MAX as u64,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for b in values {
        for c in values {
            record.add_events.push(r_type_event(
                record.add_events.len(),
                Opcode::ADD,
                b.wrapping_add(c),
                b,
                c,
            ));
        }
    }
    let chip = AddChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <AddChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 96); // 81 independent events and 15 SP1-generated padding rows.
    trace
}

fn add_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    // SP1: state, adapter, result limbs, is_real. Clean: is_real, state, adapter, result limbs.
    assert_eq!(sp1.len(), AddInstructionAirSpec::WIDTHS[0]);
    std::iter::once(sp1.last().unwrap())
        .chain(&sp1[..sp1.len() - 1])
        .map(|value| NativeField::from_u64(value.as_canonical_u64()))
        .collect()
}

fn compare<P: Program<NativeField>, S: GeneratedAirSpec>(
    sp1: &[SP1Field],
    row: &[NativeField],
    chip: &impl Air<Sp1Evaluation>,
    case: &str,
) -> bool {
    let mut expected = Sp1Evaluation {
        row: sp1.to_vec(),
        preprocessed: vec![],
        constraints: vec![],
        ledger: vec![],
        public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
    };
    chip.eval(&mut expected);
    let constraints = S::constraints::<NativeEvaluation>(0, &[], row);
    assert!(!constraints.is_empty() && !expected.constraints.is_empty());
    let valid = constraints.iter().all(|value| *value == NativeField::ZERO);
    assert_eq!(
        valid,
        expected
            .constraints
            .iter()
            .all(|value| *value == SP1Field::zero()),
        "local constraint satisfaction differs: {case}"
    );
    let mut ledger: Ledger = P::interactions(0, row)
        .into_iter()
        .map(|value| {
            (
                value.channel.to_owned(),
                value.multiplicity.as_canonical_u64(),
                value
                    .message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
            )
        })
        .collect();
    // Sorting preserves every occurrence; never filter zeros or combine repeated messages.
    ledger.sort();
    expected.ledger.sort();
    assert_eq!(
        ledger, expected.ledger,
        "complete instruction interaction multiset differs: {case}"
    );
    valid
}

fn check_trace<P: Program<NativeField>, S: GeneratedAirSpec>(
    trace: &RowMajorMatrix<SP1Field>,
    map_row: fn(&[SP1Field]) -> Vec<NativeField>,
    chip: &impl Air<Sp1Evaluation>,
) {
    assert_eq!(
        <NativeField as PrimeField64>::ORDER_U64,
        <SP1Field as Sp1PrimeField64>::ORDER_U64
    );
    assert_eq!(S::WIDTHS, &[trace.width()]);
    assert_eq!(S::FIXED_WIDTHS, &[0]);
    for (index, sp1) in trace.values.chunks(trace.width()).enumerate() {
        let row = map_row(sp1);
        let input = &row[..P::PROVER_INPUTS];
        let witness = generate::<NativeField, RowWitness<P>>(&[], input).unwrap();
        assert_eq!(
            witness.tables,
            vec![vec![row.clone()]],
            "witness row {index}"
        );
        assert!(
            compare::<P, S>(sp1, &row, chip, &format!("SP1 row {index}")),
            "SP1 row {index} must satisfy both AIRs"
        );
    }
}

fn check_mutations<P: Program<NativeField>, S: GeneratedAirSpec>(
    trace: &RowMajorMatrix<SP1Field>,
    indices: &[usize],
    map_row: fn(&[SP1Field]) -> Vec<NativeField>,
    chip: &impl Air<Sp1Evaluation>,
) {
    let mut rejected = 0;
    for &index in indices {
        let original = trace.row_slice(index);
        for column in 0..trace.width() {
            for delta in [1, 65536, <SP1Field as Sp1PrimeField64>::ORDER_U64 - 1] {
                let mut row = original.to_vec();
                row[column] += SP1Field::from_canonical_u64(delta);
                rejected += usize::from(!compare::<P, S>(
                    &row,
                    &map_row(&row),
                    chip,
                    &format!("SP1 row {index}, column {column}, delta {delta}"),
                ));
            }
        }
    }
    assert!(
        rejected > 0,
        "the mutation battery must exercise rejected constraints"
    );
}

#[test]
fn generated_add_witness_and_air_match_released_sp1() {
    let trace = add_trace();
    check_trace::<AddInstruction, AddInstructionAirSpec>(
        &trace,
        add_row,
        &AddChip::<SupervisorMode>::default(),
    );

    // Carries, wraparound and inactive padding: 396 mutations.
    check_mutations::<AddInstruction, AddInstructionAirSpec>(
        &trace,
        &[0, 40, 80, 81],
        add_row,
        &AddChip::<SupervisorMode>::default(),
    );

    check_open_buses::<AddInstruction>(&add_row(&trace.row_slice(0)));
}

fn check_open_buses<P: Program<NativeField>>(row: &[NativeField]) {
    let input = &row[..P::PROVER_INPUTS];
    let error = generate::<NativeField, P>(&[], input).unwrap_err();
    assert!(matches!(error, WitnessGenerationError::Runtime(_)));
    assert!(matches!(
        generate::<NativeField, RowWitness<P>>(&[], &input[..input.len() - 1]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

fn load_event(
    index: usize,
    opcode: Opcode,
    base: u64,
    offset: u64,
    word: u64,
    negative_immediate: bool,
    previous_window: bool,
) -> (MemInstrEvent, ITypeRecord) {
    let clk = if previous_window {
        (1 << 24) + 9
    } else {
        9 + 8 * index as u64
    };
    let c = if negative_immediate {
        offset.wrapping_sub(8)
    } else {
        offset + 8
    };
    let b = (base + offset).wrapping_sub(c);
    let selected = word >> (8 * offset);
    let a = match opcode {
        Opcode::LB => selected as u8 as i8 as i64 as u64,
        Opcode::LBU => selected as u8 as u64,
        Opcode::LH => selected as u16 as i16 as i64 as u64,
        Opcode::LHU => selected as u16 as u64,
        Opcode::LW => selected as u32 as i32 as i64 as u64,
        Opcode::LWU => selected as u32 as u64,
        Opcode::LD => selected,
        _ => unreachable!(),
    };
    let read = |value, timestamp, prev_timestamp| {
        MemoryRecordEnum::Read(MemoryReadRecord {
            value,
            timestamp,
            prev_timestamp,
            prev_page_prot_record: None,
        })
    };
    (
        MemInstrEvent {
            clk,
            pc: 4096 + 4 * index as u64,
            opcode,
            a,
            b,
            c,
            op_a_0: false,
            mem_access: read(word, clk + 1, if previous_window { 5 } else { clk - 8 }),
        },
        ITypeRecord {
            op_a: 5,
            op_b: 6,
            op_c: c,
            is_untrusted: false,
            a: MemoryRecordEnum::Write(MemoryWriteRecord {
                prev_timestamp: clk - 8,
                prev_page_prot_record: None,
                prev_value: word.rotate_left(13),
                timestamp: clk + 4,
                value: a,
            }),
            b: read(b, clk + 3, clk - 8),
        },
    )
}

fn load_byte_trace() -> RowMajorMatrix<SP1Field> {
    let mut record = ExecutionRecord::default();
    for opcode in [Opcode::LB, Opcode::LBU] {
        for base in [1 << 16, (1 << 48) - 8] {
            for word in [0, u64::MAX, 0x807f_ff00_0180_fe7f, 0x0102_0304_0506_0708] {
                for negative_immediate in [false, true] {
                    for offset in 0..8 {
                        let index = record.memory_load_byte_events.len();
                        record.memory_load_byte_events.push(load_event(
                            index,
                            opcode,
                            base,
                            offset,
                            word,
                            negative_immediate,
                            false,
                        ));
                    }
                }
            }
        }
    }
    // Exercise MemoryAccess's timestamp-high branch independently of register accesses.
    for opcode in [Opcode::LB, Opcode::LBU] {
        let index = record.memory_load_byte_events.len();
        record.memory_load_byte_events.push(load_event(
            index,
            opcode,
            1 << 32,
            7,
            0x80ff_7f00_1234_5678,
            true,
            true,
        ));
    }
    assert_eq!(record.memory_load_byte_events.len(), 258);
    let chip = LoadByteChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <LoadByteChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 288); // 258 events and 30 SP1-generated padding rows.
    trace
}

fn load_byte_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = LoadByteColumns<u8, SupervisorMode>;
    let address = offset_of!(Columns, address_operation);
    let memory = offset_of!(Columns, memory_access);
    let selectors = offset_of!(Columns, is_lb);
    assert_eq!(sp1.len(), LoadByteInstructionAirSpec::WIDTHS[0]);
    assert_eq!(selectors + 2, sp1.len());
    assert_eq!(memory - address, 4);
    // Clean places selectors first and the four witnessed address cells last.
    sp1[selectors..]
        .iter()
        .chain(&sp1[..address])
        .chain(&sp1[memory..selectors])
        .chain(&sp1[address..memory])
        .map(|value| NativeField::from_u64(value.as_canonical_u64()))
        .collect()
}

#[test]
fn generated_load_byte_witness_and_air_match_released_sp1() {
    let trace = load_byte_trace();
    check_trace::<LoadByteInstruction, LoadByteInstructionAirSpec>(
        &trace,
        load_byte_row,
        &LoadByteChip::<SupervisorMode>::default(),
    );

    // Both selectors, both address bounds, cross-window memory reads and padding.
    check_mutations::<LoadByteInstruction, LoadByteInstructionAirSpec>(
        &trace,
        &[0, 64, 128, 192, 256, 257, 258],
        load_byte_row,
        &LoadByteChip::<SupervisorMode>::default(),
    );

    check_open_buses::<LoadByteInstruction>(&load_byte_row(&trace.row_slice(0)));
}

fn div_rem_trace() -> RowMajorMatrix<SP1Field> {
    let values = [
        0,
        1,
        7,
        65535,
        65536,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 32,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [
        Opcode::DIV,
        Opcode::DIVU,
        Opcode::REM,
        Opcode::REMU,
        Opcode::DIVW,
        Opcode::REMW,
        Opcode::DIVUW,
        Opcode::REMUW,
    ] {
        for b in values {
            for c in values {
                let (quotient, remainder) = get_quotient_and_remainder(b, c, opcode);
                let a = match opcode {
                    Opcode::DIV | Opcode::DIVU | Opcode::DIVW | Opcode::DIVUW => quotient,
                    _ => remainder,
                };
                record.divrem_events.push(r_type_event(
                    record.divrem_events.len(),
                    opcode,
                    a,
                    b,
                    c,
                ));
            }
        }
    }
    assert_eq!(record.divrem_events.len(), 968);
    let chip = DivRemChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <DivRemChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 992); // Includes 24 SP1-generated "0 divided by 1" padding rows.
    trace
}

fn div_rem_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = DivRemCols<u8, SupervisorMode>;
    let mut indices = Vec::new();
    macro_rules! block {
        ($field:tt, $width:expr) => {{
            let start = offset_of!(Columns, $field);
            indices.extend(start..start + $width);
        }};
    }
    macro_rules! scalar {
        ($($field:ident),+ $(,)?) => { $(block!($field, 1);)+ };
    }
    // Native inputs: activity, reader columns and seven selectors; DIVU starts the witnesses.
    scalar!(is_real);
    indices.extend(0..offset_of!(Columns, a));
    scalar!(is_div, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw, is_divu);
    block!(quotient_comp, 4);
    block!(a, 4);
    block!(b, 4);
    block!(c, 4);
    block!(c_times_quotient_lower, 45);
    block!(c_times_quotient_upper, 45);
    scalar!(
        is_overflow,
        b_neg,
        b_neg_not_overflow,
        b_not_neg_not_overflow,
        is_real_not_word,
        rem_neg,
        c_neg
    );
    block!(c_times_quotient, 8);
    block!(carry, 8);
    block!(is_overflow_b, 11);
    block!(is_overflow_c, 11);
    block!(is_c_0, 11);
    block!(abs_c, 4);
    block!(abs_remainder, 4);
    block!(remainder_comp, 4);
    block!(max_abs_c_or_1, 4);
    block!(c_neg_operation, 4);
    block!(rem_neg_operation, 4);
    scalar!(
        abs_c_alu_event,
        abs_rem_alu_event,
        remainder_check_multiplicity
    );
    // The native less-than witness writes comparison limbs before flags, inverse and bit.
    let comparison = offset_of!(Columns, remainder_lt_operation.comparison_limbs);
    let flags = offset_of!(Columns, remainder_lt_operation.u16_flags);
    indices.extend(comparison..comparison + 2);
    indices.extend(flags..flags + 4);
    indices.push(offset_of!(Columns, remainder_lt_operation.not_eq_inv));
    indices.push(offset_of!(
        Columns,
        remainder_lt_operation.u16_compare_operation.bit
    ));
    block!(remainder, 4);
    block!(quotient, 4);
    scalar!(b_msb, c_msb, rem_msb, quot_msb);
    assert_eq!(sp1.len(), DivRemInstructionAirSpec::WIDTHS[0]);
    assert_eq!(
        <DivRemInstruction as Program<NativeField>>::PROVER_INPUTS,
        36
    );
    // Check this independent source-side map is a complete permutation, even on malformed rows.
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_div_rem_witness_and_air_match_released_sp1() {
    let trace = div_rem_trace();
    check_trace::<DivRemInstruction, DivRemInstructionAirSpec>(
        &trace,
        div_rem_row,
        &DivRemChip::<SupervisorMode>::default(),
    );

    // Zero division, signed overflow at both widths, negative operands, and nonzero padding.
    let indices: Vec<usize> = (0..8)
        .flat_map(|opcode| [0, 76, 109, 120].map(|row| opcode * 121 + row))
        .chain([968])
        .collect();
    check_mutations::<DivRemInstruction, DivRemInstructionAirSpec>(
        &trace,
        &indices,
        div_rem_row,
        &DivRemChip::<SupervisorMode>::default(),
    );

    check_open_buses::<DivRemInstruction>(&div_rem_row(&trace.row_slice(0)));
}

fn mul_trace() -> RowMajorMatrix<SP1Field> {
    let values: [u64; 11] = [
        0,
        1,
        7,
        65535,
        65536,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 32,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [
        Opcode::MUL,
        Opcode::MULH,
        Opcode::MULHU,
        Opcode::MULHSU,
        Opcode::MULW,
    ] {
        for b in values {
            for c in values {
                let a = match opcode {
                    Opcode::MUL => b.wrapping_mul(c),
                    Opcode::MULH => (((b as i64 as i128) * (c as i64 as i128)) >> 64) as u64,
                    Opcode::MULHU => (((b as u128) * (c as u128)) >> 64) as u64,
                    Opcode::MULHSU => (((b as i64 as i128) * (c as i128)) >> 64) as u64,
                    Opcode::MULW => (b as i32).wrapping_mul(c as i32) as i64 as u64,
                    _ => unreachable!(),
                };
                record
                    .mul_events
                    .push(r_type_event(record.mul_events.len(), opcode, a, b, c));
            }
        }
    }
    assert_eq!(record.mul_events.len(), 605);
    let chip = MulChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <MulChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 608); // Includes three all-zero SP1 padding rows.
    trace
}

fn mul_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = MulCols<u8, SupervisorMode>;
    // Native inputs: reader columns and selectors. Witnesses: multiplication block and result.
    // Offsets come from the independently pinned Rust struct, never the generated row inventory.
    let mut indices: Vec<usize> = (0..offset_of!(Columns, a)).collect();
    indices.extend([
        offset_of!(Columns, is_mul),
        offset_of!(Columns, is_mulh),
        offset_of!(Columns, is_mulhu),
        offset_of!(Columns, is_mulhsu),
        offset_of!(Columns, is_mulw),
    ]);
    let operation = offset_of!(Columns, mul_operation);
    indices.extend(operation..operation + 45);
    let result = offset_of!(Columns, a);
    indices.extend(result..result + 4);
    assert_eq!(sp1.len(), MulInstructionAirSpec::WIDTHS[0]);
    assert_eq!(<MulInstruction as Program<NativeField>>::PROVER_INPUTS, 33);
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_mul_witness_and_air_match_released_sp1() {
    let trace = mul_trace();
    check_trace::<MulInstruction, MulInstructionAirSpec>(
        &trace,
        mul_row,
        &MulChip::<SupervisorMode>::default(),
    );

    // Zero, word-sign boundary, signed high product, maximal limbs, and inactive padding.
    let indices: Vec<usize> = (0..5)
        .flat_map(|opcode| [0, 76, 109, 120].map(|row| opcode * 121 + row))
        .chain([605])
        .collect();
    check_mutations::<MulInstruction, MulInstructionAirSpec>(
        &trace,
        &indices,
        mul_row,
        &MulChip::<SupervisorMode>::default(),
    );

    check_open_buses::<MulInstruction>(&mul_row(&trace.row_slice(0)));
}

fn bitwise_trace() -> RowMajorMatrix<SP1Field> {
    let values: [u64; 12] = [
        0,
        1,
        255,
        256,
        65535,
        65536,
        u32::MAX as u64,
        1 << 32,
        1 << 63,
        0x5555_5555_5555_5555,
        0xaaaa_aaaa_aaaa_aaaa,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [Opcode::XOR, Opcode::OR, Opcode::AND] {
        // Register operands exercise byte/limb/word boundaries and every bit in the result.
        // Immediate operands include both signed twelve-bit boundaries and sign extension.
        let operands = values
            .into_iter()
            .flat_map(|b| values.into_iter().map(move |c| (b, c, false)))
            .chain(values.into_iter().flat_map(|b| {
                [0_i64, 1, 2047, -2048, -1]
                    .into_iter()
                    .map(move |c| (b, c as u64, true))
            }));
        for (b, c, immediate) in operands {
            let a = match opcode {
                Opcode::XOR => b ^ c,
                Opcode::OR => b | c,
                Opcode::AND => b & c,
                _ => unreachable!(),
            };
            record.bitwise_events.push(alu_type_event(
                record.bitwise_events.len(),
                opcode,
                a,
                b,
                c,
                immediate,
            ));
        }
    }
    assert_eq!(record.bitwise_events.len(), 612);
    let chip = BitwiseChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <BitwiseChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 640); // Includes 28 all-zero SP1 padding rows.
    trace
}

fn bitwise_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = BitwiseCols<u8, SupervisorMode>;
    // Reader columns and selectors are inputs; sixteen byte columns are witnesses.
    // Rust struct offsets authenticate this permutation independently of Clean's inventory.
    let operation = offset_of!(Columns, bitwise_operation);
    let mut indices: Vec<usize> = (0..operation).collect();
    indices.extend([
        offset_of!(Columns, is_xor),
        offset_of!(Columns, is_or),
        offset_of!(Columns, is_and),
    ]);
    indices.extend(operation..operation + 16);
    assert_eq!(sp1.len(), 51);
    assert_eq!(sp1.len(), BitwiseInstructionAirSpec::WIDTHS[0]);
    assert_eq!(
        <BitwiseInstruction as Program<NativeField>>::PROVER_INPUTS,
        35
    );
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_bitwise_witness_and_air_match_released_sp1() {
    let trace = bitwise_trace();
    check_trace::<BitwiseInstruction, BitwiseInstructionAirSpec>(
        &trace,
        bitwise_row,
        &BitwiseChip::<SupervisorMode>::default(),
    );

    // All three opcodes, register and immediate forms, signed boundaries, and inactive padding.
    let indices: Vec<usize> = (0..3)
        .flat_map(|opcode| {
            [0, 26, 65, 118, 143, 144, 146, 147, 148, 201, 202, 203].map(|row| opcode * 204 + row)
        })
        .chain([612])
        .collect();
    check_mutations::<BitwiseInstruction, BitwiseInstructionAirSpec>(
        &trace,
        &indices,
        bitwise_row,
        &BitwiseChip::<SupervisorMode>::default(),
    );

    check_open_buses::<BitwiseInstruction>(&bitwise_row(&trace.row_slice(0)));
}

fn lt_trace() -> RowMajorMatrix<SP1Field> {
    let values: [u64; 13] = [
        0,
        1,
        255,
        256,
        65535,
        65536,
        u32::MAX as u64,
        1 << 32,
        (1 << 48) - 1,
        1 << 48,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [Opcode::SLT, Opcode::SLTU] {
        // Equal operands, each most-significant differing limb, and opposite signs.
        // Immediate comparisons also exercise both signed twelve-bit boundaries.
        let operands = values
            .into_iter()
            .flat_map(|b| values.into_iter().map(move |c| (b, c, false)))
            .chain(values.into_iter().flat_map(|b| {
                [0_i64, 1, 2047, -2048, -1]
                    .into_iter()
                    .map(move |c| (b, c as u64, true))
            }));
        for (b, c, immediate) in operands {
            let a = match opcode {
                Opcode::SLT => ((b as i64) < (c as i64)) as u64,
                Opcode::SLTU => (b < c) as u64,
                _ => unreachable!(),
            };
            record.lt_events.push(alu_type_event(
                record.lt_events.len(),
                opcode,
                a,
                b,
                c,
                immediate,
            ));
        }
    }
    assert_eq!(record.lt_events.len(), 468);
    let chip = LtChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <LtChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 480); // Includes twelve all-zero SP1 padding rows.
    trace
}

fn lt_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = LtCols<u8, SupervisorMode>;
    // The typed inputs precede the ten comparison witnesses. Authenticate every field
    // against SP1's actual struct rather than deriving the adapter from generated output.
    let mut indices: Vec<usize> = (0..offset_of!(Columns, is_slt)).collect();
    indices.extend([
        offset_of!(Columns, is_slt),
        offset_of!(Columns, is_sltu),
        offset_of!(Columns, lt_operation.result.u16_compare_operation.bit),
    ]);
    let flags = offset_of!(Columns, lt_operation.result.u16_flags);
    indices.extend(flags..flags + 4);
    indices.push(offset_of!(Columns, lt_operation.result.not_eq_inv));
    let comparison = offset_of!(Columns, lt_operation.result.comparison_limbs);
    indices.extend(comparison..comparison + 2);
    indices.extend([
        offset_of!(Columns, lt_operation.b_msb),
        offset_of!(Columns, lt_operation.c_msb),
    ]);
    assert_eq!(sp1.len(), 44);
    assert_eq!(sp1.len(), LtInstructionAirSpec::WIDTHS[0]);
    assert_eq!(<LtInstruction as Program<NativeField>>::PROVER_INPUTS, 34);
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_lt_witness_and_air_match_released_sp1() {
    let trace = lt_trace();
    check_trace::<LtInstruction, LtInstructionAirSpec>(
        &trace,
        lt_row,
        &LtChip::<SupervisorMode>::default(),
    );

    // Both opcodes and operand forms, equal/unequal limbs, sign boundaries and padding.
    let indices: Vec<usize> = (0..2)
        .flat_map(|opcode| {
            [
                0, 1, 12, 66, 78, 91, 117, 129, 142, 155, 168, 169, 171, 172, 173, 231, 232, 233,
            ]
            .map(|row| opcode * 234 + row)
        })
        .chain([468])
        .collect();
    check_mutations::<LtInstruction, LtInstructionAirSpec>(
        &trace,
        &indices,
        lt_row,
        &LtChip::<SupervisorMode>::default(),
    );

    check_open_buses::<LtInstruction>(&lt_row(&trace.row_slice(0)));
}

fn shift_left_trace() -> RowMajorMatrix<SP1Field> {
    let values: [u64; 11] = [
        0,
        1,
        255,
        256,
        65535,
        65536,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [Opcode::SLL, Opcode::SLLW] {
        // Every effective shift amount, including bit/limb boundaries. Register operands
        // also vary the ignored high bits; immediate operands stay in their encoded range.
        let immediate_limit = if opcode == Opcode::SLL { 64 } else { 32 };
        for b in values {
            let operands = (0_u64..64)
                .chain([64, 65, 127, 65535, 1 << 32, u64::MAX])
                .map(|c| (c, false))
                .chain((0..immediate_limit).map(|c| (c, true)));
            for (c, immediate) in operands {
                let a = match opcode {
                    Opcode::SLL => b.wrapping_shl(c as u32),
                    Opcode::SLLW => (b as u32).wrapping_shl(c as u32) as i32 as i64 as u64,
                    _ => unreachable!(),
                };
                record.shift_left_events.push(alu_type_event(
                    record.shift_left_events.len(),
                    opcode,
                    a,
                    b,
                    c,
                    immediate,
                ));
            }
        }
    }
    assert_eq!(record.shift_left_events.len(), 2596);
    let chip = ShiftLeftChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <ShiftLeftChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 2624); // 28 padding rows with three nonzero power witnesses.
    trace
}

fn shift_left_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = ShiftLeftCols<u8, SupervisorMode>;
    // State, reader and explicit selectors precede the 31 generated witnesses.
    // Authenticate the full permutation using the released Rust struct's field offsets.
    let mut indices: Vec<usize> = (0..offset_of!(Columns, a)).collect();
    indices.extend([offset_of!(Columns, is_sll), offset_of!(Columns, is_sllw)]);
    indices.extend(offset_of!(Columns, a)..offset_of!(Columns, is_sll));
    indices.push(offset_of!(Columns, is_sllw_imm));
    assert_eq!(sp1.len(), 65);
    assert_eq!(sp1.len(), ShiftLeftInstructionAirSpec::WIDTHS[0]);
    assert_eq!(
        <ShiftLeftInstruction as Program<NativeField>>::PROVER_INPUTS,
        34
    );
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_shift_left_witness_and_air_match_released_sp1() {
    let trace = shift_left_trace();
    check_trace::<ShiftLeftInstruction, ShiftLeftInstructionAirSpec>(
        &trace,
        shift_left_row,
        &ShiftLeftChip::<SupervisorMode>::default(),
    );

    // Both opcodes and forms, word sign extension, split/placement boundaries and padding.
    let indices: Vec<usize> = [1, 10]
        .into_iter()
        .flat_map(|b| {
            [
                0, 1, 15, 16, 31, 32, 47, 48, 63, 64, 69, 70, 85, 86, 101, 102, 133,
            ]
            .map(|row| b * 134 + row)
        })
        .chain([7, 10].into_iter().flat_map(|b| {
            [0, 1, 15, 16, 31, 32, 63, 64, 69, 70, 85, 86, 101].map(|row| 1474 + b * 102 + row)
        }))
        .chain([0, 2596])
        .collect();
    check_mutations::<ShiftLeftInstruction, ShiftLeftInstructionAirSpec>(
        &trace,
        &indices,
        shift_left_row,
        &ShiftLeftChip::<SupervisorMode>::default(),
    );

    check_open_buses::<ShiftLeftInstruction>(&shift_left_row(&trace.row_slice(0)));
}

fn shift_right_trace() -> RowMajorMatrix<SP1Field> {
    let values: [u64; 13] = [
        0,
        1,
        255,
        256,
        65535,
        65536,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX as u64,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [Opcode::SRL, Opcode::SRA, Opcode::SRLW, Opcode::SRAW] {
        // Exercise every shift amount, word truncation and both sign boundaries.
        // High register bits are ignored; immediates stay within their encoded range.
        let immediate_limit = if matches!(opcode, Opcode::SRL | Opcode::SRA) {
            64
        } else {
            32
        };
        for b in values {
            let operands = (0_u64..64)
                .chain([64, 65, 127, 65535, 1 << 32, u64::MAX])
                .map(|c| (c, false))
                .chain((0..immediate_limit).map(|c| (c, true)));
            for (c, immediate) in operands {
                let a = match opcode {
                    Opcode::SRL => b.wrapping_shr(c as u32),
                    Opcode::SRA => (b as i64).wrapping_shr(c as u32) as u64,
                    Opcode::SRLW => (b as u32).wrapping_shr(c as u32) as i32 as i64 as u64,
                    Opcode::SRAW => (b as i32).wrapping_shr(c as u32) as i64 as u64,
                    _ => unreachable!(),
                };
                record.shift_right_events.push(alu_type_event(
                    record.shift_right_events.len(),
                    opcode,
                    a,
                    b,
                    c,
                    immediate,
                ));
            }
        }
    }
    assert_eq!(record.shift_right_events.len(), 6136);
    let chip = ShiftRightChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <ShiftRightChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 6144); // Eight padding rows with nonzero inverse powers.
    trace
}

fn shift_right_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = ShiftRightCols<u8, SupervisorMode>;
    // Authenticate all 36 inputs and 33 witnesses against SP1's physical layout.
    let mut indices: Vec<usize> = (0..offset_of!(Columns, a)).collect();
    indices.extend([
        offset_of!(Columns, is_srl),
        offset_of!(Columns, is_sra),
        offset_of!(Columns, is_srlw),
        offset_of!(Columns, is_sraw),
    ]);
    indices.extend(offset_of!(Columns, a)..offset_of!(Columns, is_srl));
    indices.push(offset_of!(Columns, is_w_imm));
    assert_eq!(sp1.len(), 69);
    assert_eq!(sp1.len(), ShiftRightInstructionAirSpec::WIDTHS[0]);
    assert_eq!(
        <ShiftRightInstruction as Program<NativeField>>::PROVER_INPUTS,
        36
    );
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_shift_right_witness_and_air_match_released_sp1() {
    let trace = shift_right_trace();
    check_trace::<ShiftRightInstruction, ShiftRightInstructionAirSpec>(
        &trace,
        shift_right_row,
        &ShiftRightChip::<SupervisorMode>::default(),
    );

    // All opcodes and forms, sign fill, limb boundaries, ignored shift bits and padding.
    let mut indices = vec![6136];
    for (base, stride) in [(0, 134), (1742, 134), (3484, 102), (4810, 102)] {
        indices.push(base); // Zero operands.
        for b in [7, 12] {
            // The word sign bit and all ones.
            indices.extend(
                [
                    0, 1, 15, 16, 31, 32, 47, 48, 63, 64, 69, 70, 85, 86, 101, 102, 133,
                ]
                .into_iter()
                .filter(|row| *row < stride)
                .map(|row| base + b * stride + row),
            );
        }
    }
    assert_eq!(indices.len(), 133); // 27,531 independent column/value mutations.
    check_mutations::<ShiftRightInstruction, ShiftRightInstructionAirSpec>(
        &trace,
        &indices,
        shift_right_row,
        &ShiftRightChip::<SupervisorMode>::default(),
    );

    check_open_buses::<ShiftRightInstruction>(&shift_right_row(&trace.row_slice(0)));
}

fn branch_trace() -> RowMajorMatrix<SP1Field> {
    let values: [u64; 9] = [
        0,
        1,
        65535,
        65536,
        u32::MAX as u64,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX,
    ];
    let mut record = ExecutionRecord::default();
    for opcode in [
        Opcode::BEQ,
        Opcode::BNE,
        Opcode::BLT,
        Opcode::BGE,
        Opcode::BLTU,
        Opcode::BGEU,
    ] {
        let mut outcomes = [0; 2];
        for a in values {
            for b in values {
                let taken = match opcode {
                    Opcode::BEQ => a == b,
                    Opcode::BNE => a != b,
                    Opcode::BLT => (a as i64) < (b as i64),
                    Opcode::BGE => (a as i64) >= (b as i64),
                    Opcode::BLTU => a < b,
                    Opcode::BGEU => a >= b,
                    _ => unreachable!(),
                };
                // Both targets fit 48 bits. Exercise zero/negative displacements and
                // carries at each PC limb boundary, for taken and fallthrough branches.
                for pc in [0x1000_u64, 0xfffc, 0xffff_fffc, (1 << 48) - 0x2000] {
                    for offset in [-4096_i64, -4, 0, 4, 4092] {
                        let c = offset as u64;
                        let next_pc = pc.wrapping_add(if taken { c } else { 4 });
                        assert!(next_pc < 1 << 48 && next_pc % 4 == 0);
                        let clk = 9 + 8 * record.branch_events.len() as u64;
                        let read = |value, timestamp| {
                            MemoryRecordEnum::Read(MemoryReadRecord {
                                value,
                                timestamp,
                                prev_timestamp: clk - 8,
                                prev_page_prot_record: None,
                            })
                        };
                        record.branch_events.push((
                            BranchEvent::new(clk, pc, next_pc, opcode, a, b, c, a == 0),
                            ITypeRecord {
                                op_a: if a == 0 { 0 } else { 5 },
                                a: read(a, clk + 4),
                                op_b: if b == 0 { 0 } else { 6 },
                                b: read(b, clk + 3),
                                op_c: c,
                                is_untrusted: false,
                            },
                        ));
                        outcomes[usize::from(taken)] += 1;
                    }
                }
            }
        }
        assert!(outcomes.iter().all(|count| *count > 0));
    }
    assert_eq!(record.branch_events.len(), 9720);
    let chip = BranchChip::<SupervisorMode>::default();
    let trace = chip.generate_trace(&record, &mut ExecutionRecord::default());
    assert_eq!(
        trace.width(),
        <BranchChip<SupervisorMode> as BaseAir<SP1Field>>::width(&chip)
    );
    assert_eq!(trace.height(), 9728); // Eight zero-filled padding rows.
    trace
}

fn branch_row(sp1: &[SP1Field]) -> Vec<NativeField> {
    type Columns = BranchColumns<u8, SupervisorMode>;
    // Authenticate the 31 input cells and all 14 witnesses using SP1's field offsets.
    let mut indices: Vec<usize> = (0..offset_of!(Columns, next_pc)).collect();
    indices.extend(offset_of!(Columns, is_beq)..offset_of!(Columns, is_branching));
    indices.extend(offset_of!(Columns, compare_operation)..offset_of!(Columns, adapter_cols));
    indices.push(offset_of!(Columns, is_branching));
    indices.extend(offset_of!(Columns, next_pc)..offset_of!(Columns, is_beq));
    assert_eq!(sp1.len(), 45);
    assert_eq!(sp1.len(), BranchInstructionAirSpec::WIDTHS[0]);
    assert_eq!(
        <BranchInstruction as Program<NativeField>>::PROVER_INPUTS,
        31
    );
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|index| NativeField::from_u64(sp1[index].as_canonical_u64()))
        .collect()
}

#[test]
fn generated_branch_witness_and_air_match_released_sp1() {
    let trace = branch_trace();
    check_trace::<BranchInstruction, BranchInstructionAirSpec>(
        &trace,
        branch_row,
        &BranchChip::<SupervisorMode>::default(),
    );

    // Every opcode, both outcomes, equality, sign boundaries, PC carries and padding.
    let indices: Vec<usize> = (0..6)
        .flat_map(|opcode| {
            [0, 1, 9, 10, 61, 69, 71, 79, 80]
                .into_iter()
                .flat_map(move |pair| {
                    [0, 6, 12, 18, 19].map(|pc_offset| opcode * 1620 + pair * 20 + pc_offset)
                })
        })
        .chain([9720])
        .collect();
    assert_eq!(indices.len(), 271); // 36,585 independent column/value mutations.
    check_mutations::<BranchInstruction, BranchInstructionAirSpec>(
        &trace,
        &indices,
        branch_row,
        &BranchChip::<SupervisorMode>::default(),
    );

    check_open_buses::<BranchInstruction>(&branch_row(&trace.row_slice(0)));
}

/// Every adapter is an independently checked permutation of the released SP1 layout.
fn reorder<P: Program<NativeField>, S: GeneratedAirSpec>(
    sp1: &[SP1Field],
    input_width: usize,
    indices: impl IntoIterator<Item = usize>,
) -> Vec<NativeField> {
    assert_eq!(S::WIDTHS, &[sp1.len()]);
    assert_eq!(P::PROVER_INPUTS, input_width);
    let indices: Vec<_> = indices.into_iter().collect();
    let mut sorted = indices.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, (0..sp1.len()).collect::<Vec<_>>());
    indices
        .into_iter()
        .map(|i| NativeField::from_u64(sp1[i].as_canonical_u64()))
        .collect()
}

fn padded_trace<C>(chip: &C, record: &ExecutionRecord, active: usize) -> RowMajorMatrix<SP1Field>
where
    C: MachineAir<SP1Field, Record = ExecutionRecord, Program = sp1_core_executor::Program>,
{
    let trace = chip.generate_trace(record, &mut ExecutionRecord::default());
    assert_eq!(trace.width(), chip.width());
    assert_eq!(trace.height(), active.div_ceil(32) * 32);
    assert!(
        active > 0 && trace.height() > active,
        "exercise active and padding rows"
    );
    trace
}

/// New families mutate every column of every event and padding row.
fn check_all_rows<P: Program<NativeField>, S: GeneratedAirSpec>(
    trace: &RowMajorMatrix<SP1Field>,
    map_row: fn(&[SP1Field]) -> Vec<NativeField>,
    chip: &impl Air<Sp1Evaluation>,
) {
    check_trace::<P, S>(trace, map_row, chip);
    check_mutations::<P, S>(
        trace,
        &(0..trace.height()).collect::<Vec<_>>(),
        map_row,
        chip,
    );
    check_open_buses::<P>(&map_row(&trace.row_slice(0)));
}

fn read_record(value: u64, timestamp: u64, prev_timestamp: u64) -> MemoryRecordEnum {
    MemoryRecordEnum::Read(MemoryReadRecord {
        value,
        timestamp,
        prev_timestamp,
        prev_page_prot_record: None,
    })
}

fn write_record(
    value: u64,
    previous: u64,
    timestamp: u64,
    prev_timestamp: u64,
) -> MemoryRecordEnum {
    MemoryRecordEnum::Write(MemoryWriteRecord {
        value,
        prev_value: previous,
        timestamp,
        prev_timestamp,
        prev_page_prot_record: None,
    })
}

const ARITHMETIC_VALUES: [u64; 11] = [
    0,
    1,
    65535,
    65536,
    (1 << 31) - 1,
    1 << 31,
    u32::MAX as u64,
    1 << 32,
    (1 << 63) - 1,
    1 << 63,
    u64::MAX,
];

fn arithmetic_record(opcode: Opcode) -> (ExecutionRecord, usize) {
    let mut record = ExecutionRecord::default();
    let mut active = 0;
    for b in ARITHMETIC_VALUES {
        let forms = if opcode == Opcode::ADDI {
            &[true][..]
        } else if opcode == Opcode::ADDW {
            &[false, true][..]
        } else {
            &[false][..]
        };
        for &immediate in forms {
            let immediates = [(-2048_i64) as u64, u64::MAX, 0, 1, 2047];
            let operands = if immediate {
                &immediates[..]
            } else {
                &ARITHMETIC_VALUES[..]
            };
            for &c in operands {
                let value = if matches!(opcode, Opcode::SUB | Opcode::SUBW) {
                    b.wrapping_sub(c)
                } else {
                    b.wrapping_add(c)
                };
                let a = if matches!(opcode, Opcode::ADDW | Opcode::SUBW) {
                    value as u32 as i32 as i64 as u64
                } else {
                    value
                };
                let (event, registers) = r_type_event(active, opcode, a, b, c);
                match opcode {
                    Opcode::ADDI => record.addi_events.push((
                        event,
                        ITypeRecord {
                            op_a: registers.op_a,
                            a: registers.a,
                            op_b: registers.op_b,
                            b: registers.b,
                            op_c: c,
                            is_untrusted: false,
                        },
                    )),
                    Opcode::ADDW => record
                        .addw_events
                        .push(alu_type_event(active, opcode, a, b, c, immediate)),
                    Opcode::SUB => record.sub_events.push((event, registers)),
                    Opcode::SUBW => record.subw_events.push((event, registers)),
                    _ => unreachable!(),
                }
                active += 1;
            }
        }
    }
    assert_eq!(
        active,
        match opcode {
            Opcode::ADDI => 55,
            Opcode::ADDW => 176,
            _ => 121,
        }
    );
    (record, active)
}

macro_rules! arithmetic_case {
    ($test:ident, $program:ident, $air:ident, $chip:ident, $cols:ident, $operation:ident, $opcode:ident) => {
        #[test]
        fn $test() {
            let (record, active) = arithmetic_record(Opcode::$opcode);
            let chip = $chip::<SupervisorMode>::default();
            let trace = padded_trace(&chip, &record, active);
            check_all_rows::<$program, $air>(
                &trace,
                |row| {
                    type Columns = $cols<u8, SupervisorMode>;
                    let real = offset_of!(Columns, is_real);
                    let operation = offset_of!(Columns, $operation);
                    assert_eq!(real + 1, row.len());
                    reorder::<$program, $air>(row, operation + 1, [real].into_iter().chain(0..real))
                },
                &chip,
            );
        }
    };
}
arithmetic_case!(
    addi,
    AddiInstruction,
    AddiInstructionAirSpec,
    AddiChip,
    AddiCols,
    add_operation,
    ADDI
);
arithmetic_case!(
    addw,
    AddwInstruction,
    AddwInstructionAirSpec,
    AddwChip,
    AddwCols,
    addw_operation,
    ADDW
);
arithmetic_case!(
    sub,
    SubInstruction,
    SubInstructionAirSpec,
    SubChip,
    SubCols,
    sub_operation,
    SUB
);
arithmetic_case!(
    subw,
    SubwInstruction,
    SubwInstructionAirSpec,
    SubwChip,
    SubwCols,
    subw_operation,
    SUBW
);

#[test]
fn alu_x0() {
    let mut record = ExecutionRecord::default();
    // All ALU discriminants that the released executor routes through its x0 chip.
    for opcode in [
        Opcode::ADD,
        Opcode::ADDI,
        Opcode::SUB,
        Opcode::XOR,
        Opcode::OR,
        Opcode::AND,
        Opcode::SLL,
        Opcode::SRL,
        Opcode::SRA,
        Opcode::SLT,
        Opcode::SLTU,
        Opcode::ADDW,
        Opcode::SUBW,
        Opcode::SLLW,
        Opcode::SRLW,
        Opcode::SRAW,
        Opcode::MUL,
        Opcode::MULH,
        Opcode::MULHU,
        Opcode::MULHSU,
        Opcode::MULW,
        Opcode::DIV,
        Opcode::DIVU,
        Opcode::REM,
        Opcode::REMU,
        Opcode::DIVW,
        Opcode::DIVUW,
        Opcode::REMW,
        Opcode::REMUW,
    ] {
        for b in ARITHMETIC_VALUES {
            for immediate in [false, true] {
                if opcode == Opcode::ADDI && !immediate {
                    continue;
                }
                if immediate && opcode.instruction_type().1.is_none() {
                    continue;
                }
                let c = if immediate { 1 } else { b.rotate_left(17) };
                let (mut event, mut registers) =
                    alu_type_event(record.alu_x0_events.len(), opcode, 0, b, c, immediate);
                event.op_a_0 = true;
                registers.op_a = 0;
                registers.a = write_record(0, 0, event.clk + 4, event.clk - 8);
                record.alu_x0_events.push((event, registers));
            }
        }
    }
    assert_eq!(record.alu_x0_events.len(), 451);
    let chip = AluX0Chip::<SupervisorMode>::default();
    let trace = padded_trace(&chip, &record, 451);
    check_all_rows::<AluX0Instruction, AluX0InstructionAirSpec>(
        &trace,
        |row| {
            type Columns = AluX0Cols<u8, SupervisorMode>;
            assert_eq!(offset_of!(Columns, adapter_cols), row.len());
            assert_eq!(offset_of!(Columns, selector_cols), row.len());
            reorder::<AluX0Instruction, AluX0InstructionAirSpec>(row, row.len(), 0..row.len())
        },
        &chip,
    );
}

#[test]
fn u_type() {
    let mut record = ExecutionRecord::default();
    for opcode in [Opcode::LUI, Opcode::AUIPC] {
        for pc in [0x1000_u64, 0xfffc, 0xffff_fffc, (1 << 48) - 8] {
            for b in [
                0,
                0x1000,
                0x7ffff000,
                0xffff_ffff_8000_0000,
                0xffff_ffff_ffff_f000,
            ] {
                for discard in [false, true] {
                    let clk = 9 + 8 * record.utype_events.len() as u64;
                    let a = if discard {
                        0
                    } else if opcode == Opcode::LUI {
                        b
                    } else {
                        pc.wrapping_add(b)
                    };
                    record.utype_events.push((
                        UTypeEvent {
                            clk,
                            pc,
                            opcode,
                            a,
                            b,
                            c: 0,
                            op_a_0: discard,
                        },
                        JTypeRecord {
                            op_a: if discard { 0 } else { 5 },
                            a: write_record(a, 0, clk + 4, clk - 8),
                            op_b: b,
                            op_c: 0,
                            is_untrusted: false,
                        },
                    ));
                }
            }
        }
    }
    assert_eq!(record.utype_events.len(), 80);
    let chip = UTypeChip::<SupervisorMode>::default();
    let trace = padded_trace(&chip, &record, 80);
    check_all_rows::<UTypeInstruction, UTypeInstructionAirSpec>(
        &trace,
        |row| {
            type Columns = UTypeColumns<u8, SupervisorMode>;
            let real = offset_of!(Columns, is_real);
            let selector = offset_of!(Columns, is_auipc);
            let witness = offset_of!(Columns, addend);
            assert_eq!(real + 1, row.len());
            reorder::<UTypeInstruction, UTypeInstructionAirSpec>(
                row,
                witness + 2,
                [real]
                    .into_iter()
                    .chain(0..witness)
                    .chain([selector])
                    .chain(witness..selector),
            )
        },
        &chip,
    );
}

#[test]
fn jal() {
    let mut record = ExecutionRecord::default();
    for pc in [0x1000_u64, 0xfffc, 0xffff_fffc, (1 << 48) - 0x2000] {
        for offset in [-4096_i64, -4, 0, 4, 4092] {
            for discard in [false, true] {
                let clk = 9 + 8 * record.jal_events.len() as u64;
                let a = if discard { 0 } else { pc + 4 };
                let b = offset as u64;
                let next_pc = pc.wrapping_add(b);
                assert!(next_pc < 1 << 48 && next_pc % 4 == 0);
                record.jal_events.push((
                    JumpEvent {
                        clk,
                        pc,
                        next_pc,
                        opcode: Opcode::JAL,
                        a,
                        b,
                        c: 0,
                        op_a_0: discard,
                    },
                    JTypeRecord {
                        op_a: if discard { 0 } else { 5 },
                        a: write_record(a, 0, clk + 4, clk - 8),
                        op_b: b,
                        op_c: 0,
                        is_untrusted: false,
                    },
                ));
            }
        }
    }
    assert_eq!(record.jal_events.len(), 40);
    let chip = JalChip::<SupervisorMode>::default();
    let trace = padded_trace(&chip, &record, 40);
    check_all_rows::<JalInstruction, JalInstructionAirSpec>(
        &trace,
        |row| {
            type Columns = JalColumns<u8, SupervisorMode>;
            let real = offset_of!(Columns, is_real);
            assert_eq!(real + 1, row.len());
            reorder::<JalInstruction, JalInstructionAirSpec>(
                row,
                offset_of!(Columns, add_operation) + 1,
                [real].into_iter().chain(0..real),
            )
        },
        &chip,
    );
}

#[test]
fn jalr() {
    let mut record = ExecutionRecord::default();
    for pc in [0x1000_u64, 0xfffc, 0xffff_fffc, (1 << 48) - 8] {
        for target in [0, 0xfffc_u64, 1 << 32, (1 << 48) - 4] {
            for immediate in [-2048_i64, -1, 0, 1, 2047] {
                for lsb in [0, 1] {
                    for discard in [false, true] {
                        let clk = 9 + 8 * record.jalr_events.len() as u64;
                        let c = immediate as u64;
                        let b = (target + lsb).wrapping_sub(c);
                        let a = if discard { 0 } else { pc + 4 };
                        record.jalr_events.push((
                            JumpEvent {
                                clk,
                                pc,
                                next_pc: target,
                                opcode: Opcode::JALR,
                                a,
                                b,
                                c,
                                op_a_0: discard,
                            },
                            ITypeRecord {
                                op_a: if discard { 0 } else { 5 },
                                a: write_record(a, 0, clk + 4, clk - 8),
                                op_b: if b == 0 { 0 } else { 6 },
                                b: read_record(b, clk + 3, clk - 8),
                                op_c: c,
                                is_untrusted: false,
                            },
                        ));
                    }
                }
            }
        }
    }
    // Add a distinct x0 source/destination case, and ensure the trace has padding.
    let clk = 9 + 8 * record.jalr_events.len() as u64;
    record.jalr_events.push((
        JumpEvent {
            clk,
            pc: 4096,
            next_pc: 0,
            opcode: Opcode::JALR,
            a: 0,
            b: 0,
            c: 0,
            op_a_0: true,
        },
        ITypeRecord {
            op_a: 0,
            a: write_record(0, 0, clk + 4, clk - 8),
            op_b: 0,
            b: read_record(0, clk + 3, clk - 8),
            op_c: 0,
            is_untrusted: false,
        },
    ));
    assert_eq!(record.jalr_events.len(), 321);
    let chip = JalrChip::<SupervisorMode>::default();
    let trace = padded_trace(&chip, &record, 321);
    check_all_rows::<JalrInstruction, JalrInstructionAirSpec>(
        &trace,
        |row| {
            type Columns = JalrColumns<u8, SupervisorMode>;
            let real = offset_of!(Columns, is_real);
            assert_eq!(real + 1, offset_of!(Columns, add_operation));
            reorder::<JalrInstruction, JalrInstructionAirSpec>(
                row,
                real + 1,
                [real].into_iter().chain(0..real).chain(real + 1..row.len()),
            )
        },
        &chip,
    );
}

fn load_events(opcodes: &[Opcode], discard: bool) -> Vec<(MemInstrEvent, ITypeRecord)> {
    let mut events = vec![];
    for &opcode in opcodes {
        let alignment = match opcode {
            Opcode::LB | Opcode::LBU => 1,
            Opcode::LH | Opcode::LHU => 2,
            Opcode::LW | Opcode::LWU => 4,
            Opcode::LD => 8,
            _ => unreachable!(),
        };
        for base in [1 << 16, (1 << 48) - 8] {
            for word in [0, u64::MAX, 0x807f_ff00_0180_fe7f, 0x0102_0304_0506_0708] {
                for negative in [false, true] {
                    for offset in (0..8).step_by(alignment) {
                        events.push(load_event(
                            events.len(),
                            opcode,
                            base,
                            offset,
                            word,
                            negative,
                            false,
                        ));
                    }
                }
            }
        }
        events.push(load_event(
            events.len(),
            opcode,
            1 << 32,
            8 - alignment as u64,
            0x80ff_7f00_1234_5678,
            true,
            true,
        ));
    }
    if discard {
        for (event, registers) in &mut events {
            event.a = 0;
            event.op_a_0 = true;
            registers.op_a = 0;
            registers.a = write_record(0, 0, event.clk + 4, event.clk - 8);
        }
    }
    events
}

// The native memory chips take selectors first and compute four address limbs last.
macro_rules! memory_row {
    ($row:expr, $program:ident, $air:ident, $cols:ident, $selector:ident) => {{
        type Columns = $cols<u8, SupervisorMode>;
        let row = $row;
        let address = offset_of!(Columns, address_operation);
        let memory = offset_of!(Columns, memory_access);
        let selectors = offset_of!(Columns, $selector);
        assert_eq!(memory - address, 4);
        assert_eq!(offset_of!(Columns, adapter_cols), row.len());
        reorder::<$program, $air>(
            row,
            row.len() - 4,
            (selectors..row.len())
                .chain(0..address)
                .chain(memory..selectors)
                .chain(address..memory),
        )
    }};
}

macro_rules! load_case {
    ($test:ident, $program:ident, $air:ident, $chip:ident, $cols:ident, $selector:ident,
     $events:ident, $opcodes:expr, $discard:literal, $active:literal) => {
        #[test]
        fn $test() {
            let mut record = ExecutionRecord::default();
            record.$events = load_events($opcodes, $discard);
            assert_eq!(record.$events.len(), $active);
            let chip = $chip::<SupervisorMode>::default();
            let trace = padded_trace(&chip, &record, $active);
            check_all_rows::<$program, $air>(
                &trace,
                |row| memory_row!(row, $program, $air, $cols, $selector),
                &chip,
            );
        }
    };
}
load_case!(
    load_half,
    LoadHalfInstruction,
    LoadHalfInstructionAirSpec,
    LoadHalfChip,
    LoadHalfColumns,
    is_lh,
    memory_load_half_events,
    &[Opcode::LH, Opcode::LHU],
    false,
    130
);
load_case!(
    load_word,
    LoadWordInstruction,
    LoadWordInstructionAirSpec,
    LoadWordChip,
    LoadWordColumns,
    is_lw,
    memory_load_word_events,
    &[Opcode::LW, Opcode::LWU],
    false,
    66
);
load_case!(
    load_double,
    LoadDoubleInstruction,
    LoadDoubleInstructionAirSpec,
    LoadDoubleChip,
    LoadDoubleColumns,
    is_real,
    memory_load_double_events,
    &[Opcode::LD],
    false,
    17
);
load_case!(
    load_x0,
    LoadX0Instruction,
    LoadX0InstructionAirSpec,
    LoadX0Chip,
    LoadX0Columns,
    is_lb,
    memory_load_x0_events,
    &[
        Opcode::LB,
        Opcode::LBU,
        Opcode::LH,
        Opcode::LHU,
        Opcode::LW,
        Opcode::LWU,
        Opcode::LD
    ],
    true,
    471
);

fn store_event(
    index: usize,
    opcode: Opcode,
    base: u64,
    offset: u64,
    previous: u64,
    value: u64,
    negative: bool,
    previous_window: bool,
) -> (MemInstrEvent, ITypeRecord) {
    let clk = if previous_window {
        (1 << 24) + 9
    } else {
        9 + 8 * index as u64
    };
    let c = if negative {
        offset.wrapping_sub(8)
    } else {
        offset + 8
    };
    let b = (base + offset).wrapping_sub(c);
    let mask = match opcode {
        Opcode::SB => 0xff,
        Opcode::SH => 0xffff,
        Opcode::SW => 0xffff_ffff,
        Opcode::SD => u64::MAX,
        _ => unreachable!(),
    };
    let shift = 8 * offset;
    let stored = (previous & !(mask << shift)) | ((value & mask) << shift);
    let memory_previous = if previous_window { 5 } else { clk - 8 };
    (
        MemInstrEvent {
            clk,
            pc: 4096 + 4 * index as u64,
            opcode,
            a: value,
            b,
            c,
            op_a_0: value == 0,
            mem_access: write_record(stored, previous, clk + 1, memory_previous),
        },
        ITypeRecord {
            op_a: if value == 0 { 0 } else { 5 },
            a: read_record(value, clk + 4, clk - 8),
            op_b: 6,
            b: read_record(b, clk + 3, clk - 8),
            op_c: c,
            is_untrusted: false,
        },
    )
}

fn store_events(opcode: Opcode) -> Vec<(MemInstrEvent, ITypeRecord)> {
    let alignment = match opcode {
        Opcode::SB => 1,
        Opcode::SH => 2,
        Opcode::SW => 4,
        Opcode::SD => 8,
        _ => unreachable!(),
    };
    let mut events = vec![];
    for base in [1 << 16, (1 << 48) - 8] {
        for previous in [0, u64::MAX, 0x807f_ff00_0180_fe7f] {
            for value in [0, 1, u64::MAX, 0x0102_0304_0506_0708] {
                for negative in [false, true] {
                    for offset in (0..8).step_by(alignment) {
                        events.push(store_event(
                            events.len(),
                            opcode,
                            base,
                            offset,
                            previous,
                            value,
                            negative,
                            false,
                        ));
                    }
                }
            }
        }
    }
    events.push(store_event(
        events.len(),
        opcode,
        1 << 32,
        8 - alignment as u64,
        0x80ff_7f00_1234_5678,
        0xff80_017f_ffff_0000,
        true,
        true,
    ));
    events
}

macro_rules! store_case {
    ($test:ident, $program:ident, $air:ident, $chip:ident, $cols:ident,
     $events:ident, $opcode:ident, $active:literal) => {
        #[test]
        fn $test() {
            let mut record = ExecutionRecord::default();
            record.$events = store_events(Opcode::$opcode);
            assert_eq!(record.$events.len(), $active);
            let chip = $chip::<SupervisorMode>::default();
            let trace = padded_trace(&chip, &record, $active);
            check_all_rows::<$program, $air>(
                &trace,
                |row| memory_row!(row, $program, $air, $cols, is_real),
                &chip,
            );
        }
    };
}
store_case!(
    store_byte,
    StoreByteInstruction,
    StoreByteInstructionAirSpec,
    StoreByteChip,
    StoreByteColumns,
    memory_store_byte_events,
    SB,
    385
);
store_case!(
    store_half,
    StoreHalfInstruction,
    StoreHalfInstructionAirSpec,
    StoreHalfChip,
    StoreHalfColumns,
    memory_store_half_events,
    SH,
    193
);
store_case!(
    store_word,
    StoreWordInstruction,
    StoreWordInstructionAirSpec,
    StoreWordChip,
    StoreWordColumns,
    memory_store_word_events,
    SW,
    97
);
store_case!(
    store_double,
    StoreDoubleInstruction,
    StoreDoubleInstructionAirSpec,
    StoreDoubleChip,
    StoreDoubleColumns,
    memory_store_double_events,
    SD,
    49
);
