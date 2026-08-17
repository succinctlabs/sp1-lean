//! Reference interpreter for the Lean-exported witness-generation IR.
//!
//! Consumes the `version: 1` wire format documented in `docs/witgen-wire-format.md`
//! (normative source: the Clean pin's `Clean/Circuit/WitnessExport.lean`), and runs
//! the differential fixtures under `export/testdata/`. Deliberately self-contained:
//! the crate depends only on the wire format — no prover types, no Lean toolchain.
//!
//! Witness generation is completeness-side: a wrong interpreter (or a wrong exported
//! program) makes a prover fail, never a false proof verify — this crate is a
//! conformance oracle, not a trusted component.

pub mod eval;
pub mod field;
pub mod fixtures;
pub mod wire;

use field::KoalaBear;
use std::path::Path;

/// Run the differential battery. Returns `(rows checked, failure messages)`.
pub fn run_all(
    export_dir: &Path,
    chip: Option<&str>,
    verbose: bool,
) -> Result<(usize, Vec<String>), String> {
    let chips = fixtures::chips_in(export_dir, chip)?;
    let mut rows = 0;
    let mut failures = Vec::new();
    for chip in &chips {
        let report = fixtures::run_chip::<KoalaBear>(export_dir, chip, verbose)?;
        let status = if report.failures.is_empty() {
            "ok"
        } else {
            "FAIL"
        };
        println!("{}: {} rows {status}", report.chip, report.rows);
        rows += report.rows;
        failures.extend(report.failures);
    }
    Ok((rows, failures))
}
