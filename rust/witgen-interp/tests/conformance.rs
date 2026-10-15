//! The differential battery as a cargo test: every fixture row under
//! the freshly generated `testdata/` must reproduce its expected witness cells exactly.
//! `scripts/check_witgen_export.py` supplies `WITGEN_EXPORT_DIR` after validating coverage.

use std::path::PathBuf;

#[test]
fn all_fixture_rows_reproduce() {
    let dir = std::env::var("WITGEN_EXPORT_DIR")
        .map(PathBuf::from)
        .expect("set WITGEN_EXPORT_DIR to a fresh scripts/check_witgen_export.py output directory");
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
