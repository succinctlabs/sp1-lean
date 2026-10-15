//! Native providers prove byte membership; SP1 authenticates a preprocessed table.
//! Compare messages with the actual released AIR without equating those physical layouts.

extern crate alloc;

#[path = "support/export.rs"]
mod export_support;

use clean_backend::witness_generation::{generate, Program, WitnessGenerationError};
use clean_backend::GeneratedAirSpec;
use export_support::{Ledger, NativeEvaluation, RowWitness, Sp1Evaluation};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;
use slop_air::Air;
use slop_algebra::{AbstractField, PrimeField64 as Sp1PrimeField64};
use slop_matrix::Matrix;
use sp1_core_executor::Program as Sp1Program;
use sp1_core_machine::bytes::{ByteChip, NUM_BYTE_OPS};
use sp1_hypercube::air::{MachineAir, SP1_PROOF_NUM_PV_ELTS};
use sp1_primitives::SP1Field;

macro_rules! generated_byte {
    ($module:ident, $file:literal, $program:ident, $air:ident) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
        use $module::{$air, $program};
    };
}
generated_byte!(
    and_byte,
    "and_byte_provider.rs",
    AndByteProvider,
    AndByteProviderAirSpec
);
generated_byte!(
    or_byte,
    "or_byte_provider.rs",
    OrByteProvider,
    OrByteProviderAirSpec
);
generated_byte!(
    xor_byte,
    "xor_byte_provider.rs",
    XorByteProvider,
    XorByteProviderAirSpec
);
generated_byte!(
    range_byte,
    "u8_range_byte_provider.rs",
    U8RangeByteProvider,
    U8RangeByteProviderAirSpec
);
generated_byte!(
    ltu_byte,
    "ltu_byte_provider.rs",
    LtuByteProvider,
    LtuByteProviderAirSpec
);
generated_byte!(
    msb_byte,
    "msb_byte_provider.rs",
    MsbByteProvider,
    MsbByteProviderAirSpec
);

fn input<P: Program<F>>(b: u64, c: u64, multiplicity: u64) -> Vec<F> {
    match P::PROVER_INPUTS {
        2 => vec![F::from_u64(b), F::from_u64(multiplicity)],
        3 => vec![F::from_u64(b), F::from_u64(c), F::from_u64(multiplicity)],
        width => panic!("unexpected byte input width {width}"),
    }
}

fn valid<S: GeneratedAirSpec>(row: &[F]) -> bool {
    let constraints = S::constraints::<NativeEvaluation>(0, &[], row);
    assert!(!constraints.is_empty());
    constraints.iter().all(|value| *value == F::ZERO)
}

fn check<P: Program<F>, S: GeneratedAirSpec>(b: u64, c: u64, count: u64, mutate: bool) -> Ledger {
    assert_eq!(P::COMPONENTS, 1);
    assert_eq!(S::FIXED_WIDTHS, &[0]);
    let inputs = input::<P>(b, c, count);
    let witness = generate::<F, RowWitness<P>>(&[], &inputs).unwrap();
    assert_eq!(witness.tables.len(), 1);
    assert_eq!(witness.tables[0].len(), 1);
    let row = &witness.tables[0][0];
    assert_eq!(S::WIDTHS, &[row.len()]);
    assert_eq!(&row[..inputs.len()], inputs);
    assert!(valid::<S>(row));
    if mutate {
        for column in 0..row.len() {
            for delta in [1, 256, F::ORDER_U64 - 1] {
                let mut changed = row.clone();
                changed[column] += F::from_u64(delta);
                // Multiplicity is an unconstrained input; all other cells are uniquely determined.
                assert_eq!(
                    valid::<S>(&changed),
                    column == inputs.len() - 1,
                    "byte row ({b}, {c}, {count}), column {column}, delta {delta}"
                );
            }
        }
    }
    let ledger: Ledger = P::interactions(0, row)
        .into_iter()
        .map(|entry| {
            (
                entry.channel.to_owned(),
                entry.multiplicity.as_canonical_u64(),
                entry
                    .message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
            )
        })
        .collect();
    assert_eq!(ledger.len(), 1, "keep the zero-multiplicity occurrence");
    ledger
}

#[test]
fn all_byte_pairs_and_counts_match_released_preprocessing_and_air() {
    assert_eq!(F::ORDER_U64, <SP1Field as Sp1PrimeField64>::ORDER_U64);
    let chip = ByteChip::<SP1Field>::default();
    let trace = chip
        .generate_preprocessed_trace(&Sp1Program::default())
        .unwrap();
    assert_eq!((trace.height(), trace.width()), (65536, 7));
    assert_eq!(NUM_BYTE_OPS, 6);
    let providers: [fn(u64, u64, u64, bool) -> Ledger; 6] = [
        check::<AndByteProvider, AndByteProviderAirSpec>,
        check::<OrByteProvider, OrByteProviderAirSpec>,
        check::<XorByteProvider, XorByteProviderAirSpec>,
        check::<U8RangeByteProvider, U8RangeByteProviderAirSpec>,
        check::<LtuByteProvider, LtuByteProviderAirSpec>,
        check::<MsbByteProvider, MsbByteProviderAirSpec>,
    ];
    let counts = [0, 1, 2, F::ORDER_U64 - 1];
    let edges = [0, 1, 127, 128, 254, 255];
    for (index, row) in trace.values.chunks(trace.width()).enumerate() {
        let b = row[0].as_canonical_u64();
        let c = row[1].as_canonical_u64();
        assert_eq!((b, c), ((index >> 8) as u64, (index & 255) as u64));
        for round in 0..counts.len() {
            let multiplicities: Vec<_> = (0..6).map(|op| counts[(round + op) % 4]).collect();
            let mut expected = Sp1Evaluation {
                row: multiplicities
                    .iter()
                    .copied()
                    .map(SP1Field::from_canonical_u64)
                    .collect(),
                preprocessed: row.to_vec(),
                constraints: vec![],
                ledger: vec![],
                public: vec![SP1Field::zero(); SP1_PROOF_NUM_PV_ELTS],
            };
            chip.eval(&mut expected);
            assert!(
                expected.constraints.is_empty(),
                "SP1 authenticates the fixed table"
            );
            assert_eq!(expected.ledger.len(), 6);
            let mut actual: Ledger = providers
                .iter()
                .enumerate()
                .flat_map(|(op, provider)| {
                    provider(
                        b,
                        c,
                        multiplicities[op],
                        edges.contains(&b) && edges.contains(&c),
                    )
                })
                .collect();
            assert_eq!(actual.len(), 6);
            // Preserve all occurrences, repeated MSB keys, zero counts and aggregate counts.
            actual.sort();
            expected.ledger.sort();
            assert_eq!(
                actual, expected.ledger,
                "byte pair ({b}, {c}), count round {round}"
            );
        }
    }
}

fn malformed<P: Program<F>, S: GeneratedAirSpec>() {
    for count in [0, 1, 2, F::ORDER_U64 - 1] {
        for operand in 0..P::PROVER_INPUTS - 1 {
            for value in [256, 257, 65536, F::ORDER_U64 - 1] {
                let mut inputs = input::<P>(0, 0, count);
                inputs[operand] = F::from_u64(value);
                let witness = generate::<F, RowWitness<P>>(&[], &inputs).unwrap();
                assert!(
                    !valid::<S>(&witness.tables[0][0]),
                    "non-byte input must fail even at count zero"
                );
            }
        }
    }
    assert!(matches!(
        generate::<F, RowWitness<P>>(&[], &[]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

#[test]
fn out_of_range_inputs_are_rejected_independently_of_multiplicity() {
    malformed::<AndByteProvider, AndByteProviderAirSpec>();
    malformed::<OrByteProvider, OrByteProviderAirSpec>();
    malformed::<XorByteProvider, XorByteProviderAirSpec>();
    malformed::<U8RangeByteProvider, U8RangeByteProviderAirSpec>();
    malformed::<LtuByteProvider, LtuByteProviderAirSpec>();
    malformed::<MsbByteProvider, MsbByteProviderAirSpec>();
}

fn open_bus<P: Program<F>, S: GeneratedAirSpec>() {
    let padding = P::padding();
    assert_eq!(padding.len(), 1);
    assert_eq!(padding[0].input, input::<P>(0, 0, 0));
    let witness = generate::<F, P>(&[], &input::<P>(0, 0, 0)).unwrap();
    assert!(valid::<S>(&witness.tables[0][0]));
    for count in [1, 2, F::ORDER_U64 - 1] {
        assert!(
            matches!(
                generate::<F, P>(&[], &input::<P>(127, 255, count)),
                Err(WitnessGenerationError::Runtime(_))
            ),
            "open byte bus must not balance"
        );
    }
}

#[test]
fn zero_padding_balances_but_unmatched_provider_rows_do_not() {
    open_bus::<AndByteProvider, AndByteProviderAirSpec>();
    open_bus::<OrByteProvider, OrByteProviderAirSpec>();
    open_bus::<XorByteProvider, XorByteProviderAirSpec>();
    open_bus::<U8RangeByteProvider, U8RangeByteProviderAirSpec>();
    open_bus::<LtuByteProvider, LtuByteProviderAirSpec>();
    open_bus::<MsbByteProvider, MsbByteProviderAirSpec>();
}
