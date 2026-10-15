extern crate alloc;

// Clean's renderer emits reusable helpers that this small fixture does not all exercise.
#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod generated {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/fixed_membership.rs"
    ));
}

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod registers {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/snapshot_registers.rs"
    ));
}

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod empty_registers {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/snapshot_registers_empty.rs"
    ));
}

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod target_registers {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/target_registers.rs"
    ));
}

#[allow(dead_code, unused_imports, unused_variables, unused_parens)]
mod empty_target_registers {
    include!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/target_registers_empty.rs"
    ));
}

use clean_backend::witness_generation::{Program, WitnessGenerationError};
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleShapeError, GeneratedAirSpec, GeneratedEnsemble,
    StarkConfig,
};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_fri::{create_test_fri_params, TwoAdicFriPcs};
use p3_koala_bear::{KoalaBear as F, Poseidon2KoalaBear};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::{rngs::SmallRng, SeedableRng};

type Perm = Poseidon2KoalaBear<16>;
type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type Mmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, Hash, Compress, 8>;
type Challenge = BinomialExtensionField<F, 4>;
type ChallengeMmcs = ExtensionMmcs<F, Challenge, Mmcs>;
type Challenger = DuplexChallenger<F, Perm, 16, 8>;
type Pcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, Mmcs, ChallengeMmcs>;
type Config = StarkConfig<Pcs, Challenge, Challenger>;

fn config() -> Config {
    let mut rng = SmallRng::seed_from_u64(7);
    let permutation = Perm::new_from_rng_128(&mut rng);
    let mmcs = Mmcs::new(
        Hash::new(permutation.clone()),
        Compress::new(permutation.clone()),
    );
    let fri = create_test_fri_params(ChallengeMmcs::new(mmcs.clone()), 0);
    let pcs = Pcs::new(Radix2DitParallel::default(), mmcs, fri);
    Config::new(pcs, Challenger::new(permutation))
}

fn field(value: u64) -> F {
    F::from_u64(value)
}

#[test]
fn generated_witnesses_match_lean_and_independent_fixed_membership() {
    let reference: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/fixed_membership.reference.json"
    )))
    .unwrap();
    assert_eq!(reference.as_array().unwrap().len(), 3);
    assert_eq!(F::ORDER_U64, 2_130_706_433);
    for (case, value) in reference.as_array().unwrap().iter().zip([7, 9, 8]) {
        assert_eq!(case["publicInput"], value);
        assert_eq!(case["accepted"], value != 8);
        let generated = generated::generate(&[field(value)], &[]);
        if value == 8 {
            assert!(generated.is_err(), "forged membership must fail");
            continue;
        }
        let witness = generated.unwrap();
        let tables = witness
            .tables
            .iter()
            .map(|table| {
                table
                    .iter()
                    .map(|row| row.iter().map(|x| x.as_canonical_u64()).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(serde_json::json!(tables), case["tables"]);
        assert_eq!(
            tables,
            vec![vec![
                vec![7, u64::from(value == 7), 49],
                vec![9, u64::from(value == 9), 81]
            ]]
        );
        assert_eq!(case["interactionCount"], 3);
        let statement = generated::FixedMembershipStatement::<F>::new(&[2]).unwrap();
        assert_eq!(
            statement.interaction_count(),
            3,
            "zero-count rows retain their occurrence"
        );
        let traces = witness.into_traces().unwrap();
        assert_eq!((traces[0].height(), traces[0].width()), (2, 2));
        let fixed = generated::FixedMembershipAirSpec::fixed_trace::<F>(0).unwrap();
        assert_eq!(fixed.values, vec![field(7), field(9)]);
    }
    assert!(matches!(
        generated::generate::<F>(&[], &[]),
        Err(WitnessGenerationError::PublicInputWidth { .. })
    ));
    assert!(matches!(
        generated::generate(&[field(7)], &[field(1)]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
}

#[test]
fn generated_air_proves_and_binds_the_public_value() {
    let config = config();
    let statement = generated::FixedMembershipStatement::<F>::new(&[2]).unwrap();
    for value in [7, 9] {
        let public = [field(value)];
        let traces = generated::generate(&public, &[])
            .unwrap()
            .into_traces()
            .unwrap();
        let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).unwrap();
        for wrong in [8, if value == 7 { 9 } else { 7 }] {
            assert!(verify_ensemble(&config, &statement, &proof, &[field(wrong)]).is_err());
        }
    }
}

#[test]
fn generated_air_rejects_wrong_shape_and_row_content() {
    let config = config();
    let statement = generated::FixedMembershipStatement::<F>::new(&[2]).unwrap();
    assert!(matches!(
        generated::FixedMembershipStatement::<F>::new(&[]),
        Err(EnsembleShapeError::ComponentCount { .. })
    ));
    assert!(matches!(
        generated::FixedMembershipStatement::<F>::new(&[2, 2]),
        Err(EnsembleShapeError::ComponentCount { .. })
    ));
    assert!(matches!(
        generated::FixedMembershipStatement::<F>::new(&[4]),
        Err(EnsembleShapeError::FixedTraceHeight { .. })
    ));
    let public = [field(7)];
    let traces = generated::generate(&public, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    assert!(matches!(
        prove_ensemble(&config, &statement, vec![], &public),
        Err(EnsembleShapeError::TraceCount { .. })
    ));
    assert!(matches!(
        prove_ensemble(
            &config,
            &statement,
            vec![traces[0].clone(), traces[0].clone()],
            &public
        ),
        Err(EnsembleShapeError::TraceCount { .. })
    ));
    assert!(matches!(
        prove_ensemble(
            &config,
            &statement,
            vec![RowMajorMatrix::new(vec![field(1), field(0)], 1)],
            &public
        ),
        Err(EnsembleShapeError::TraceWidth { .. })
    ));

    // Release mode reaches verification for invalid witnesses; debug mode may reject them earlier.
    for (cell, value) in [(0, 0), (0, 2), (1, 64), (2, 1)] {
        let mut altered = traces.clone();
        altered[0].values[cell] = field(value);
        assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, altered, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
    }
    assert_eq!(
        <generated::FixedMembership as Program<F>>::COMPONENT_NAMES,
        &["allowed"]
    );
}

// Release mode verifies a rejected proof; debug mode can reject invalid constraints earlier.
// Propagate unrelated panics instead of treating an arbitrary crash as rejection.
fn assert_backend_rejection(check: impl FnOnce() -> bool) {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(check)) {
        Ok(rejected) => assert!(rejected, "invalid witness was accepted"),
        Err(payload) => {
            let message = payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| payload.downcast_ref::<&str>().copied())
                .unwrap_or("");
            if !cfg!(debug_assertions)
                || !(message.contains("constraint") || message.contains("lookup"))
            {
                std::panic::resume_unwind(payload);
            }
        }
    }
}

// This arbitrary local snapshot is not SP1's boot-only all-zero register table.
// Compute its values and Memory records independently of generated Lean metadata.
fn register(index: u64) -> Vec<u64> {
    assert!(index < 32);
    let value = index.wrapping_mul(0x0123_4567_89ab_cdef);
    let mut row = vec![index];
    row.extend((0..4).map(|limb| (value >> (16 * limb)) & 0xffff));
    row
}

fn eligible_register(index: u64) -> Vec<u64> {
    [register(index), vec![1]].concat()
}

// These expected rows come from the input list, independently of Lean/exported metadata.
fn padded_membership_rows(source: &[u64], public: &[u64]) -> Vec<Vec<u64>> {
    (0..source.len().next_power_of_two())
        .map(|index| {
            let value = source.get(index).copied().unwrap_or(0);
            let eligible = index < source.len() && !source[..index].contains(&value);
            let count = if eligible {
                public.iter().filter(|request| **request == value).count() as u64
            } else {
                0
            };
            vec![value, u64::from(eligible), count]
        })
        .collect()
}

fn check_padded_membership<P: Program<F>, S: GeneratedAirSpec>(
    source: &[u64],
    public: &[u64],
    reference: &serde_json::Value,
) {
    let rows = padded_membership_rows(source, public);
    let height = rows.len();
    assert_eq!(P::FIXED_WIDTHS, &[2]);
    let fixed = S::fixed_trace::<F>(0).unwrap();
    assert_eq!((fixed.height(), fixed.width()), (height, 2));
    assert_eq!(
        fixed.values,
        rows.iter()
            .flat_map(|row| row[..2].iter().copied())
            .map(field)
            .collect::<Vec<_>>()
    );
    let public_fields: Vec<_> = public.iter().copied().map(field).collect();
    let result = clean_backend::witness_generation::generate::<F, P>(&public_fields, &[]);
    let accepted = public.iter().all(|value| source.contains(value));
    assert_eq!(result.is_ok(), accepted);
    if !public.is_empty() {
        assert_eq!(reference["publicInput"], serde_json::json!(public));
        assert_eq!(reference["accepted"], accepted);
    }
    let Ok(witness) = result else { return };
    let actual = physical_reference::<P>(&public_fields, &witness.tables);
    assert_eq!(
        &actual,
        if public.is_empty() {
            reference
        } else {
            &reference["witness"]
        }
    );
    let ledger: Vec<_> = public
        .iter()
        .map(|value| {
            interaction(
                "fixture.membership",
                F::ORDER_U64 - 1,
                vec![*value, 1],
                true,
            )
        })
        .chain(
            rows.iter()
                .map(|row| interaction("fixture.membership", row[2], row[..2].to_vec(), false)),
        )
        .collect();
    assert_eq!(
        actual,
        serde_json::json!({"tables": [rows], "interactions": ledger})
    );
    let statement = GeneratedEnsemble::<F, S>::new(&[height]).unwrap();
    assert_eq!(
        statement.interaction_count(),
        (height + public.len()) as u128
    );
    for invalid in [0, height + 1, height * 2] {
        assert!(GeneratedEnsemble::<F, S>::new(&[invalid]).is_err());
    }
    let config = config();
    let traces = witness.into_traces().unwrap();
    assert_eq!((traces[0].height(), traces[0].width()), (height, 1));
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public_fields).unwrap();
    verify_ensemble(&config, &statement, &proof, &public_fields).unwrap();
    for cell in 0..public.len() {
        let mut altered = public_fields.clone();
        altered[cell] += field(1);
        assert!(verify_ensemble(&config, &statement, &proof, &altered).is_err());
    }
    // Includes every real, duplicate and padding row, in both directions.
    for row in 0..height {
        for delta in [field(1), -field(1)] {
            let mut altered = traces.clone();
            altered[0].values[row] += delta;
            assert_backend_rejection(|| {
                let (proof, _) =
                    prove_ensemble(&config, &statement, altered, &public_fields).unwrap();
                verify_ensemble(&config, &statement, &proof, &public_fields).is_err()
            });
        }
    }

    // Identical inactive messages can cancel in the ledger. Their nonzero counts must still
    // violate the AIR constraint, independently of the lookup balance check.
    if let Some((first, second)) = (0..height).find_map(|first| {
        (first + 1..height)
            .find(|&second| rows[first][1] == 0 && rows[first][..2] == rows[second][..2])
            .map(|second| (first, second))
    }) {
        for delta in [field(1), -field(1)] {
            let mut altered = traces.clone();
            altered[0].values[first] += delta;
            altered[0].values[second] -= delta;
            let interactions = [first, second].map(|index| {
                let mut row: Vec<_> = rows[index].iter().copied().map(field).collect();
                row[2] = altered[0].values[index];
                P::interactions(0, &row)
            });
            assert_eq!(interactions[0].len(), 1);
            assert_eq!(interactions[1].len(), 1);
            let left = &interactions[0][0];
            let right = &interactions[1][0];
            assert_eq!(left.channel, "fixture.membership");
            assert_eq!(left.channel, right.channel);
            assert_eq!(left.message, vec![field(rows[first][0]), field(0)]);
            assert_eq!(left.message, right.message);
            assert!(!left.assume_guarantees && !right.assume_guarantees);
            assert_eq!(left.multiplicity, delta);
            assert_eq!(right.multiplicity, -delta);
            assert_backend_rejection(|| {
                let (proof, _) =
                    prove_ensemble(&config, &statement, altered, &public_fields).unwrap();
                verify_ensemble(&config, &statement, &proof, &public_fields).is_err()
            });
        }
    }
}

macro_rules! padded_membership_fixture {
    ($module:ident, $name:literal, $source:expr) => {
        mod $module {
            use super::*;
            #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
            mod used {
                include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/static_", $name, ".rs"));
            }
            #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
            mod unused {
                include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/static_", $name, "_unused.rs"));
            }
            #[test]
            fn independent_rows_ledgers_and_backend_mutations() {
                let fixtures: serde_json::Value = serde_json::from_str(include_str!(concat!(
                    env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/static_membership.reference.json"
                ))).unwrap();
                assert_eq!(fixtures.as_array().unwrap().len(), 5);
                let fixture = fixtures.as_array().unwrap().iter().find(|f| f["name"] == $name).unwrap();
                let cases = fixture["cases"].as_array().unwrap();
                assert_eq!(cases.len(), 16);
                for (index, (a, b)) in [0, 7, 9, 11].into_iter()
                    .flat_map(|a| [0, 7, 9, 11].into_iter().map(move |b| (a, b))).enumerate()
                {
                    check_padded_membership::<used::StaticMembership, used::StaticMembershipAirSpec>(
                        $source, &[a, b], &cases[index]);
                }
                check_padded_membership::<unused::UnusedMembership, unused::UnusedMembershipAirSpec>(
                    $source, &[], &fixture["unused"]);
            }
        }
    };
}

padded_membership_fixture!(empty_membership, "empty", &[]);
padded_membership_fixture!(singleton_membership, "singleton", &[0]);
padded_membership_fixture!(uneven_membership, "uneven", &[7, 0, 9]);
padded_membership_fixture!(duplicate_membership, "duplicates", &[0, 7, 0, 7, 9]);
padded_membership_fixture!(zero_membership, "zeroes", &[0, 0, 0, 0, 0]);

fn memory(row: &[u64]) -> Vec<u64> {
    let mut message = vec![0, 0, row[0], 0, 0];
    message.extend_from_slice(&row[1..]);
    message
}

fn interaction(channel: &str, mult: u64, message: Vec<u64>, assumes: bool) -> serde_json::Value {
    serde_json::json!({
        "channel": channel, "message": message,
        "multiplicity": mult, "assumeGuarantees": assumes,
    })
}

fn physical_reference<P: Program<F>>(public: &[F], tables: &[Vec<Vec<F>>]) -> serde_json::Value {
    let interactions = P::verifier_interactions(public)
        .into_iter()
        .chain(tables.iter().enumerate().flat_map(|(component, rows)| {
            rows.iter()
                .flat_map(move |row| P::interactions(component, row))
        }))
        .map(|entry| {
            interaction(
                entry.channel,
                entry.multiplicity.as_canonical_u64(),
                entry
                    .message
                    .iter()
                    .map(PrimeField64::as_canonical_u64)
                    .collect(),
                entry.assume_guarantees,
            )
        })
        .collect::<Vec<_>>();
    let rows = tables
        .iter()
        .map(|table| {
            table
                .iter()
                .map(|row| {
                    row.iter()
                        .map(PrimeField64::as_canonical_u64)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    serde_json::json!({"tables": rows, "interactions": interactions})
}

fn register_reference() -> serde_json::Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/snapshot_registers.reference.json"
    )))
    .unwrap()
}

#[test]
fn snapshot_registers_match_source_values_and_complete_lean_ledger() {
    let reference = register_reference();
    let mut cases: Vec<_> = (0..32)
        .map(|index| {
            (
                format!("register-{index}"),
                [register(index), register(31)].concat(),
                true,
            )
        })
        .collect();
    cases.push((
        "repeated".to_owned(),
        [register(5), register(5)].concat(),
        true,
    ));
    for limb in 0..4 {
        let mut forged = register(5);
        forged[limb + 1] += 1;
        cases.push((
            format!("forged-limb-{limb}"),
            [forged, register(31)].concat(),
            false,
        ));
    }
    for index in [6, 32, 0] {
        let mut forged = register(5);
        forged[0] = index;
        cases.push((
            format!("forged-index-{index}"),
            [forged, register(31)].concat(),
            false,
        ));
    }
    assert_eq!(reference["cases"].as_array().unwrap().len(), cases.len());
    assert_eq!(cases.len(), 40);
    assert_eq!(
        <registers::SnapshotRegisters as Program<F>>::FIXED_WIDTHS,
        &[0, 6]
    );
    let fixed = registers::SnapshotRegistersAirSpec::fixed_trace::<F>(1).unwrap();
    assert_eq!((fixed.height(), fixed.width()), (32, 6));
    assert_eq!(
        fixed.values,
        (0..32)
            .flat_map(eligible_register)
            .map(field)
            .collect::<Vec<_>>()
    );

    for (case, (name, public, accepted)) in reference["cases"].as_array().unwrap().iter().zip(cases)
    {
        assert_eq!(case["name"], name);
        assert_eq!(case["publicInput"], serde_json::json!(public));
        assert_eq!(case["accepted"], accepted);
        let public_fields: Vec<_> = public.iter().copied().map(field).collect();
        let result = registers::generate(&public_fields, &[]);
        assert_eq!(result.is_ok(), accepted, "{name}");
        if !accepted {
            continue;
        }
        let witness = result.unwrap();
        let actual =
            physical_reference::<registers::SnapshotRegisters>(&public_fields, &witness.tables);
        assert_eq!(actual, case["witness"], "{name}");
        let sparse: Vec<Vec<u64>> = public.chunks_exact(5).map(<[u64]>::to_vec).collect();
        let fixed_rows: Vec<Vec<u64>> = (0..32)
            .map(|index| {
                let mut row = eligible_register(index);
                row.push(sparse.iter().filter(|r| r[0] == index).count() as u64);
                row
            })
            .collect();
        assert_eq!(actual["tables"], serde_json::json!([sparse, fixed_rows]));
        let mut ledger: Vec<_> = sparse
            .iter()
            .map(|row| interaction("SP1Memory", F::ORDER_U64 - 1, memory(row), true))
            .collect();
        for row in &sparse {
            ledger.push(interaction(
                "sp1.native.source_registers",
                F::ORDER_U64 - 1,
                [row.clone(), vec![1]].concat(),
                true,
            ));
            ledger.push(interaction("SP1Memory", 1, memory(row), false));
        }
        for row in fixed_rows {
            ledger.push(interaction(
                "sp1.native.source_registers",
                row[6],
                row[..6].to_vec(),
                false,
            ));
        }
        assert_eq!(actual["interactions"], serde_json::json!(ledger));
        assert_eq!(
            ledger.len(),
            38,
            "keep all repeated and zero-count occurrences"
        );
        let statement = registers::SnapshotRegistersStatement::<F>::new(&[2, 32]).unwrap();
        assert_eq!(statement.interaction_count(), 38);
        let traces = witness.into_traces().unwrap();
        assert_eq!((traces[0].height(), traces[0].width()), (2, 5));
        assert_eq!((traces[1].height(), traces[1].width()), (32, 1));
    }
}

#[test]
fn unused_snapshot_registers_keep_all_fixed_rows_and_zero_occurrences() {
    let witness = empty_registers::generate::<F>(&[], &[]).unwrap();
    let actual =
        physical_reference::<empty_registers::EmptySnapshotRegisters>(&[], &witness.tables);
    assert_eq!(actual, register_reference()["empty"]);
    let rows: Vec<_> = (0..32)
        .map(|index| {
            let mut row = eligible_register(index);
            row.push(0);
            row
        })
        .collect();
    let ledger: Vec<_> = (0..32)
        .map(|index| {
            interaction(
                "sp1.native.source_registers",
                0,
                eligible_register(index),
                false,
            )
        })
        .collect();
    assert_eq!(
        actual,
        serde_json::json!({"tables": [rows], "interactions": ledger})
    );
    let statement = empty_registers::EmptySnapshotRegistersStatement::<F>::new(&[32]).unwrap();
    assert_eq!(statement.interaction_count(), 32);
    let config = config();
    let traces = witness.into_traces().unwrap();
    assert_eq!((traces[0].height(), traces[0].width()), (32, 1));
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &[]).unwrap();
    verify_ensemble(&config, &statement, &proof, &[]).unwrap();
    for index in [0, 5, 31] {
        let mut altered = traces.clone();
        altered[0].values[index] = field(1);
        let (proof, _) = prove_ensemble(&config, &statement, altered, &[]).unwrap();
        assert!(verify_ensemble(&config, &statement, &proof, &[]).is_err());
    }
}

#[test]
fn snapshot_register_proofs_bind_each_public_index_and_limb() {
    let config = config();
    let statement = registers::SnapshotRegistersStatement::<F>::new(&[2, 32]).unwrap();
    for indices in [[0, 31], [5, 5]] {
        let public: Vec<_> = indices.into_iter().flat_map(register).map(field).collect();
        let traces = registers::generate(&public, &[])
            .unwrap()
            .into_traces()
            .unwrap();
        let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).unwrap();
        for cell in 0..public.len() {
            let mut changed = public.clone();
            changed[cell] += field(1);
            assert!(verify_ensemble(&config, &statement, &proof, &changed).is_err());
        }
    }
}

#[test]
fn snapshot_register_air_rejects_shapes_sparse_row_and_count_mutations() {
    for heights in [vec![], vec![32], vec![2, 32, 32], vec![2, 16], vec![2, 64]] {
        assert!(registers::SnapshotRegistersStatement::<F>::new(&heights).is_err());
    }
    assert!(matches!(
        registers::generate::<F>(&[], &[]),
        Err(WitnessGenerationError::PublicInputWidth { .. })
    ));
    let public: Vec<_> = [5, 31].into_iter().flat_map(register).map(field).collect();
    assert!(matches!(
        registers::generate(&public, &[field(1)]),
        Err(WitnessGenerationError::ProverInputWidth { .. })
    ));
    let traces = registers::generate(&public, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    let config = config();
    let statement = registers::SnapshotRegistersStatement::<F>::new(&[2, 32]).unwrap();
    assert!(matches!(
        prove_ensemble(&config, &statement, vec![traces[0].clone()], &public),
        Err(EnsembleShapeError::TraceCount { .. })
    ));
    // Fixed values are verifier-owned and absent from committed traces. Mutate every
    // sparse index/limb and every count, including unused counts, in both directions.
    for (table, trace) in traces.iter().enumerate() {
        for cell in 0..trace.values.len() {
            for delta in [field(1), -field(1)] {
                let mut changed = traces.clone();
                changed[table].values[cell] += delta;
                let (proof, _) = prove_ensemble(&config, &statement, changed, &public).unwrap();
                assert!(
                    verify_ensemble(&config, &statement, &proof, &public).is_err(),
                    "accepted mutation of table {table}, cell {cell}"
                );
            }
        }
    }
}

fn final_register(index: u64, clock: u64) -> Vec<u64> {
    let mut row = memory(&register(index));
    row[0] = clock >> 24;
    row[1] = clock & ((1 << 24) - 1);
    row
}

fn target_register_reference() -> serde_json::Value {
    serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/target_registers.reference.json"
    )))
    .unwrap()
}

#[test]
fn target_registers_match_complete_receipts_and_independent_fixed_values() {
    let reference = target_register_reference();
    let last = final_register(31, (2 << 24) + 31);
    let row = final_register(5, (1 << 24) + 5);
    let mut cases: Vec<_> = (0..32)
        .map(|index| {
            (
                format!("register-{index}"),
                [final_register(index, (1 << 24) + index), last.clone()].concat(),
                true,
            )
        })
        .collect();
    cases.push((
        "repeated".to_owned(),
        [row.clone(), row.clone()].concat(),
        true,
    ));
    for limb in 0..4 {
        let mut forged = row.clone();
        forged[limb + 5] += 1;
        cases.push((
            format!("forged-limb-{limb}"),
            [forged, last.clone()].concat(),
            false,
        ));
    }
    for index in [6, 32, 0] {
        let mut forged = row.clone();
        forged[2] = index;
        cases.push((
            format!("forged-index-{index}"),
            [forged, last.clone()].concat(),
            false,
        ));
    }
    for limb in [1, 2] {
        let mut forged = row.clone();
        forged[limb + 2] = 1;
        cases.push((
            format!("forged-addr{limb}"),
            [forged, last.clone()].concat(),
            false,
        ));
    }
    assert_eq!(cases.len(), 42);
    assert_eq!(reference["cases"].as_array().unwrap().len(), cases.len());
    assert_eq!(
        <target_registers::TargetRegisters as Program<F>>::FIXED_WIDTHS,
        &[0, 6]
    );
    let fixed = target_registers::TargetRegistersAirSpec::fixed_trace::<F>(1).unwrap();
    assert_eq!((fixed.height(), fixed.width()), (32, 6));
    assert_eq!(
        fixed.values,
        (0..32)
            .flat_map(eligible_register)
            .map(field)
            .collect::<Vec<_>>()
    );
    let config = config();
    let statement = target_registers::TargetRegistersStatement::<F>::new(&[2, 32]).unwrap();
    for (case, (name, public, accepted)) in reference["cases"].as_array().unwrap().iter().zip(cases)
    {
        assert_eq!(case["name"], name);
        assert_eq!(case["publicInput"], serde_json::json!(public));
        assert_eq!(case["accepted"], accepted);
        let public: Vec<_> = public.into_iter().map(field).collect();
        let result = target_registers::generate(&public, &[]);
        assert_eq!(result.is_ok(), case["witness"].is_object(), "{name}");
        let Ok(witness) = result else {
            assert!(!accepted, "{name}");
            continue;
        };
        let actual =
            physical_reference::<target_registers::TargetRegisters>(&public, &witness.tables);
        assert_eq!(actual, case["witness"], "{name}");
        let sparse: Vec<Vec<u64>> = public
            .chunks_exact(9)
            .map(|row| row.iter().map(PrimeField64::as_canonical_u64).collect())
            .collect();
        let fixed_rows: Vec<Vec<u64>> = (0..32)
            .map(|index| {
                let mut row = eligible_register(index);
                row.push(sparse.iter().filter(|r| r[2] == index).count() as u64);
                row
            })
            .collect();
        assert_eq!(actual["tables"], serde_json::json!([sparse, fixed_rows]));
        let mut ledger: Vec<_> = sparse
            .iter()
            .map(|row| interaction("SP1FinalRegisterValue", 1, row.clone(), false))
            .collect();
        for row in &sparse {
            let membership = [vec![row[2]], row[5..].to_vec(), vec![1]].concat();
            ledger.push(interaction(
                "sp1.native.target_registers",
                F::ORDER_U64 - 1,
                membership,
                true,
            ));
            ledger.push(interaction(
                "SP1FinalRegisterValue",
                F::ORDER_U64 - 1,
                row.clone(),
                true,
            ));
        }
        for row in fixed_rows {
            ledger.push(interaction(
                "sp1.native.target_registers",
                row[6],
                row[..6].to_vec(),
                false,
            ));
        }
        assert_eq!(actual["interactions"], serde_json::json!(ledger));
        assert_eq!(ledger.len(), 38);
        assert_eq!(statement.interaction_count(), 38);
        let traces = witness.into_traces().unwrap();
        assert_eq!((traces[0].height(), traces[0].width()), (2, 9));
        assert_eq!((traces[1].height(), traces[1].width()), (32, 1));
        // Malformed upper address limbs can balance and generate rows while failing AIR.
        if !accepted {
            assert_backend_rejection(|| {
                let (proof, _) = prove_ensemble(&config, &statement, traces, &public).unwrap();
                verify_ensemble(&config, &statement, &proof, &public).is_err()
            });
        }
    }
}

#[test]
fn unused_target_registers_retain_every_zero_count_occurrence() {
    let witness = empty_target_registers::generate::<F>(&[], &[]).unwrap();
    let actual =
        physical_reference::<empty_target_registers::EmptyTargetRegisters>(&[], &witness.tables);
    assert_eq!(actual, target_register_reference()["empty"]);
    let rows: Vec<_> = (0..32)
        .map(|index| {
            let mut row = eligible_register(index);
            row.push(0);
            row
        })
        .collect();
    let ledger: Vec<_> = (0..32)
        .map(|index| {
            interaction(
                "sp1.native.target_registers",
                0,
                eligible_register(index),
                false,
            )
        })
        .collect();
    assert_eq!(
        actual,
        serde_json::json!({"tables": [rows], "interactions": ledger})
    );
    let statement = empty_target_registers::EmptyTargetRegistersStatement::<F>::new(&[32]).unwrap();
    assert_eq!(statement.interaction_count(), 32);
    let config = config();
    let traces = witness.into_traces().unwrap();
    assert_eq!((traces[0].height(), traces[0].width()), (32, 1));
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &[]).unwrap();
    verify_ensemble(&config, &statement, &proof, &[]).unwrap();
    for index in [0, 5, 31] {
        let mut altered = traces.clone();
        altered[0].values[index] = field(1);
        let (proof, _) = prove_ensemble(&config, &statement, altered, &[]).unwrap();
        assert!(verify_ensemble(&config, &statement, &proof, &[]).is_err());
    }
}

#[test]
fn target_register_backend_binds_clocks_values_addresses_and_counts() {
    for heights in [vec![], vec![32], vec![2, 32, 32], vec![2, 16], vec![2, 64]] {
        assert!(target_registers::TargetRegistersStatement::<F>::new(&heights).is_err());
    }
    assert!(matches!(
        target_registers::generate::<F>(&[], &[]),
        Err(WitnessGenerationError::PublicInputWidth { .. })
    ));
    let statement = target_registers::TargetRegistersStatement::<F>::new(&[2, 32]).unwrap();
    let config = config();
    for indices in [[0, 31], [5, 5]] {
        let public: Vec<_> = indices
            .into_iter()
            .map(|index| final_register(index, (1 << 24) + index))
            .flatten()
            .map(field)
            .collect();
        assert!(matches!(
            target_registers::generate(&public, &[field(1)]),
            Err(WitnessGenerationError::ProverInputWidth { .. })
        ));
        let traces = target_registers::generate(&public, &[])
            .unwrap()
            .into_traces()
            .unwrap();
        assert!(matches!(
            prove_ensemble(&config, &statement, vec![traces[0].clone()], &public),
            Err(EnsembleShapeError::TraceCount { .. })
        ));
        let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).unwrap();
        for cell in 0..public.len() {
            let mut altered = public.clone();
            altered[cell] += field(1);
            assert!(verify_ensemble(&config, &statement, &proof, &altered).is_err());
        }
        // Both clock limbs, every address/value limb, and all 32 counts remain bound.
        for (table, trace) in traces.iter().enumerate() {
            for cell in 0..trace.values.len() {
                for delta in [field(1), -field(1)] {
                    let mut altered = traces.clone();
                    altered[table].values[cell] += delta;
                    assert_backend_rejection(|| {
                        let (proof, _) =
                            prove_ensemble(&config, &statement, altered, &public).unwrap();
                        verify_ensemble(&config, &statement, &proof, &public).is_err()
                    });
                }
            }
        }
    }
}

#[path = "support/ram.rs"]
#[allow(dead_code)]
mod ram;

fn check_ram_membership<P: Program<F>, S: GeneratedAirSpec>(name: &str) {
    let reference: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/ram_membership.reference.json"
    )))
    .unwrap();
    let source = ram::intervals();
    let first = ram::interval(65536, 65537, 17);
    let mut requests: Vec<_> = source
        .iter()
        .map(|row| ([row.clone(), first.clone()].concat(), true))
        .collect();
    requests.push(([first.clone(), first.clone()].concat(), true));
    for bad in [
        ram::interval(65536, 65537, 99),
        ram::interval(65535, 65537, 17),
        ram::interval(65536, 65538, 17),
    ] {
        requests.push(([bad, first.clone()].concat(), false));
    }
    assert_eq!(P::FIXED_WIDTHS, &[10]);
    let fixed = S::fixed_trace::<F>(0).unwrap();
    assert_eq!((fixed.height(), fixed.width()), (16, 10));
    let fixed_rows: Vec<_> = (0..16)
        .map(|index| {
            source
                .get(index)
                .map(|row| [row.clone(), vec![1]].concat())
                .unwrap_or(vec![0; 10])
        })
        .collect();
    assert_eq!(
        fixed.values,
        fixed_rows
            .iter()
            .flatten()
            .copied()
            .map(field)
            .collect::<Vec<_>>()
    );
    let cases = reference[name].as_array().unwrap();
    assert_eq!(cases.len(), requests.len());
    for ((public, accepted), case) in requests.iter().zip(cases) {
        assert_eq!(case["publicInput"], serde_json::json!(public));
        assert_eq!(case["accepted"], *accepted);
        let fields: Vec<_> = public.iter().copied().map(field).collect();
        let result = clean_backend::witness_generation::generate::<F, P>(&fields, &[]);
        assert_eq!(result.is_ok(), *accepted);
        let Ok(witness) = result else { continue };
        let rows: Vec<_> = fixed_rows
            .iter()
            .map(|row| {
                let count = if row[9] == 1 {
                    public
                        .chunks_exact(9)
                        .filter(|request| *request == &row[..9])
                        .count() as u64
                } else {
                    0
                };
                [row.clone(), vec![count]].concat()
            })
            .collect();
        let ledger: Vec<_> = public
            .chunks_exact(9)
            .map(|row| {
                interaction(
                    name,
                    F::ORDER_U64 - 1,
                    [row.to_vec(), vec![1]].concat(),
                    true,
                )
            })
            .chain(
                rows.iter()
                    .map(|row| interaction(name, row[10], row[..10].to_vec(), false)),
            )
            .collect();
        let actual = physical_reference::<P>(&fields, &witness.tables);
        assert_eq!(
            actual,
            serde_json::json!({"tables": [rows], "interactions": ledger})
        );
        assert_eq!(actual, case["witness"]);
    }
    let public: Vec<_> = [first.clone(), first]
        .concat()
        .into_iter()
        .map(field)
        .collect();
    let statement = GeneratedEnsemble::<F, S>::new(&[16]).unwrap();
    assert_eq!(statement.interaction_count(), 18);
    for height in [0, 8, 32] {
        assert!(GeneratedEnsemble::<F, S>::new(&[height]).is_err());
    }
    let traces = clean_backend::witness_generation::generate::<F, P>(&public, &[])
        .unwrap()
        .into_traces()
        .unwrap();
    assert_eq!((traces[0].height(), traces[0].width()), (16, 1));
    let config = config();
    let (proof, _) = prove_ensemble(&config, &statement, traces.clone(), &public).unwrap();
    verify_ensemble(&config, &statement, &proof, &public).unwrap();
    for cell in 0..public.len() {
        let mut forged = public.clone();
        forged[cell] += field(1);
        assert!(verify_ensemble(&config, &statement, &proof, &forged).is_err());
    }
    // Every demanded, unused, empty-interval and padding row retains a bound count.
    for row in 0..16 {
        let mut forged = traces.clone();
        forged[0].values[row] += field(1);
        assert_backend_rejection(|| {
            let (proof, _) = prove_ensemble(&config, &statement, forged, &public).unwrap();
            verify_ensemble(&config, &statement, &proof, &public).is_err()
        });
    }
    // Equal padding messages can cancel; eligibility must still forbid both nonzero counts.
    let mut forged = traces.clone();
    forged[0].values[14] = field(1);
    forged[0].values[15] = -field(1);
    assert_backend_rejection(|| {
        let (proof, _) = prove_ensemble(&config, &statement, forged, &public).unwrap();
        verify_ensemble(&config, &statement, &proof, &public).is_err()
    });
}

macro_rules! ram_membership_fixture {
    ($module:ident, $file:literal, $program:ident, $air:ident, $channel:literal) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
            #[test]
            fn interval_rows_counts_and_backend_mutations() {
                super::check_ram_membership::<$program, $air>($channel);
            }
        }
    };
}
ram_membership_fixture!(
    source_ram,
    "ram_source_membership.rs",
    RamSourceMembership,
    RamSourceMembershipAirSpec,
    "sp1.native.initial_memory"
);
ram_membership_fixture!(
    target_ram,
    "ram_target_membership.rs",
    RamTargetMembership,
    RamTargetMembershipAirSpec,
    "sp1.native.target_memory"
);
