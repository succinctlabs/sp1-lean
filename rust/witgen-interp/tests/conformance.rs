//! The differential battery as a cargo test: every fixture row under
//! `export/testdata/` must reproduce its expected witness cells exactly.
//! Override the export location with `WITGEN_EXPORT_DIR`.

use std::path::PathBuf;

#[test]
fn all_fixture_rows_reproduce() {
    let dir = std::env::var("WITGEN_EXPORT_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("../../export"));
    let (rows, failures) =
        witgen_interp::run_all(&dir, None, false).expect("export dir readable and well-formed");
    assert!(rows > 0, "no fixture rows found");
    assert!(
        failures.is_empty(),
        "{} mismatches:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
