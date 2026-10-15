//! Native RAM semantics and Clean lowering checks. SP1's release Byte AIR is compared separately.
//! Component rows keep their external channels open; these are not whole-execution proofs.

extern crate alloc;

use clean_backend::witness_generation::{generate, Program};
use clean_backend::GeneratedAirSpec;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as F;

#[path = "support/ram.rs"]
mod ram;
// The shared adapter also serves the SP1 AIR tests; RAM uses its native half.
#[path = "support/export.rs"]
#[allow(dead_code)]
mod support;
use support::{NativeEvaluation, RowWitness};

macro_rules! generated {
    ($module:ident, $file:literal) => {
        #[allow(dead_code, unused_imports, unused_variables, unused_parens)]
        mod $module {
            include!(concat!(env!("CLEAN_ENSEMBLE_EXPORT_DIR"), "/", $file));
        }
    };
}
generated!(byte, "ram_byte.rs");
generated!(word, "ram_word.rs");
generated!(source, "ram_source.rs");
generated!(target, "ram_target.rs");

fn fields(values: &[u64]) -> Vec<F> {
    values.iter().copied().map(F::from_u64).collect()
}
fn values(row: &[F]) -> Vec<u64> {
    row.iter().map(PrimeField64::as_canonical_u64).collect()
}
fn unpack(word: &[u64]) -> u64 {
    word.iter()
        .enumerate()
        .map(|(i, limb)| limb << (16 * i))
        .sum()
}

fn byte_valid(message: &[u64]) -> bool {
    let [op, a, b, c] = *message else {
        return false;
    };
    match op {
        0 => b < 256 && c < 256 && a == b & c,
        1 => b < 256 && c < 256 && a == b | c,
        2 => b < 256 && c < 256 && a == b ^ c,
        3 => a == 0 && b < 256 && c < 256,
        4 => b < 256 && c < 256 && a == u64::from(b < c),
        5 => b < 256 && c == 0 && a == b >> 7,
        6 => b <= 16 && a < 1 << b && c == 0,
        _ => false,
    }
}

fn valid<P: Program<F>, S: GeneratedAirSpec>(row: &[F]) -> bool {
    let intervals = ram::intervals();
    S::constraints::<NativeEvaluation>(0, &[], row)
        .iter()
        .all(|value| *value == F::ZERO)
        && P::interactions(0, row).iter().all(|entry| {
            if entry.multiplicity == F::ZERO {
                return true;
            }
            let message = values(&entry.message);
            match entry.channel {
                "SP1Byte" => byte_valid(&message),
                "sp1.native.initial_memory" | "sp1.native.target_memory" => {
                    message.len() == 10
                        && message[9] == 1
                        && intervals.iter().any(|row| row == &message[..9])
                }
                "SP1Memory" | "SP1FinalRamValue" => true,
                other => panic!("unexpected channel {other}"),
            }
        })
}

fn check<P: Program<F>, S: GeneratedAirSpec>(kind: &str, width: usize) {
    let reference: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CLEAN_ENSEMBLE_EXPORT_DIR"),
        "/ram_rows.reference.json"
    )))
    .unwrap();
    let addresses = [
        0,
        31,
        32,
        65529,
        65536,
        65537,
        65543,
        131064,
        131065,
        131072,
        ram::LIMIT - 8,
        ram::LIMIT - 7,
        ram::LIMIT - 1,
        ram::LIMIT,
    ];
    let mut inputs: Vec<Vec<u64>> = addresses
        .iter()
        .map(|&address| {
            if kind == "target" {
                [
                    vec![3, 17],
                    ram::word(address)[..3].to_vec(),
                    ram::word(ram::value(address)),
                ]
                .concat()
            } else {
                ram::word(address)
            }
        })
        .collect();
    if kind == "target" {
        inputs.extend([
            vec![3, 17, 0, 1, 0, 99, 0, 0, 0],
            vec![3, 17, 65536, 0, 0, 17, 0, 0, 0],
        ]);
    } else {
        inputs.push(vec![65536, 0, 0, 0]);
    }
    let cases = reference[kind].as_array().unwrap();
    assert_eq!(cases.len(), inputs.len());
    assert_eq!(P::FIXED_WIDTHS, &[0]);
    for (input, case) in inputs.iter().zip(cases) {
        assert_eq!(case["input"], serde_json::json!(input));
        let input_fields = fields(input);
        let witness = generate::<F, RowWitness<P>>(&[], &input_fields).unwrap();
        let row = &witness.tables[0][0];
        assert_eq!(row.len(), width);
        assert_eq!(serde_json::json!(values(row)), case["row"]);
        let actual = P::interactions(0, row);
        let ledger: Vec<_> = actual.iter().map(|entry| serde_json::json!({
            "channel": entry.channel, "message": values(&entry.message),
            "multiplicity": entry.multiplicity.as_canonical_u64(), "assumeGuarantees": entry.assume_guarantees,
        })).collect();
        assert_eq!(serde_json::json!(ledger), case["interactions"]);
        let address_limbs = if kind == "target" {
            &input[2..5]
        } else {
            &input[..]
        };
        let address = unpack(address_limbs);
        let expected = address_limbs.iter().all(|limb| *limb < 65536)
            && address < ram::LIMIT
            && (kind == "byte" || address <= ram::LIMIT - 8)
            && (kind != "source" || address >= 65536 && address % 8 == 0)
            && (kind != "target" || input[5..] == ram::word(ram::value(address)));
        assert_eq!(valid::<P, S>(row), expected, "{kind}: {input:?}");
        assert!(
            generate::<F, P>(&[], &input_fields).is_err(),
            "open RAM buses must not balance"
        );
        if !expected {
            continue;
        }
        let membership: Vec<_> = actual
            .iter()
            .filter(|entry| entry.channel.ends_with("_memory"))
            .collect();
        assert_eq!(membership.len(), if kind == "byte" { 1 } else { 8 });
        for (offset, entry) in membership.iter().enumerate() {
            assert_eq!(
                entry.channel,
                if kind == "target" {
                    "sp1.native.target_memory"
                } else {
                    "sp1.native.initial_memory"
                }
            );
            assert_eq!(entry.multiplicity, -F::ONE);
            assert!(entry.assume_guarantees);
            let message = values(&entry.message);
            assert!(unpack(&message[..4]) <= address + offset as u64);
            assert!(address + (offset as u64) < unpack(&message[4..8]));
            assert_eq!(message[8], ram::byte(address + offset as u64));
            assert_eq!(message[9], 1);
        }
        if kind == "source" || kind == "target" {
            let channel = if kind == "source" {
                "SP1Memory"
            } else {
                "SP1FinalRamValue"
            };
            let records: Vec<_> = actual
                .iter()
                .filter(|entry| entry.channel == channel)
                .collect();
            assert_eq!(records.len(), 1);
            let expected_record = if kind == "source" {
                [
                    vec![0, 0],
                    ram::word(address)[..3].to_vec(),
                    ram::word(ram::value(address)),
                ]
                .concat()
            } else {
                input.clone()
            };
            assert_eq!(values(&records[0].message), expected_record);
            assert_eq!(
                records[0].multiplicity,
                if kind == "source" { F::ONE } else { -F::ONE }
            );
        }
    }
    // Exercise all committed cells of a live row. Bus-bound fields can remain locally free;
    // constraints and independently checked Byte/membership predicates must reject many changes.
    let input = &inputs[4];
    let witness = generate::<F, RowWitness<P>>(&[], &fields(input)).unwrap();
    let row = &witness.tables[0][0];
    let rejected = (0..row.len())
        .filter(|&cell| {
            let mut forged = row.clone();
            forged[cell] += F::ONE;
            !valid::<P, S>(&forged)
        })
        .count();
    assert!(
        rejected > row.len() / 2,
        "mutation battery must exercise the actual constraints"
    );
}

#[test]
fn byte_rows() {
    check::<byte::RamByte, byte::RamByteAirSpec>("byte", 93);
}
#[test]
fn word_rows() {
    check::<word::RamWord, word::RamWordAirSpec>("word", 744);
}
#[test]
fn source_rows() {
    check::<source::RamSource, source::RamSourceAirSpec>("source", 748);
}
#[test]
fn target_rows() {
    check::<target::RamTarget, target::RamTargetAirSpec>("target", 749);
}
