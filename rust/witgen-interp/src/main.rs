//! CLI for the witgen reference interpreter.
//!
//! ```text
//! witgen-interp check --export-dir DIR [--chip NAME] [--verbose]
//! ```
//!
//! Exit codes: 0 = every fixture row reproduced its expected witness cells;
//! 1 = at least one mismatch (each reported with chip / row / cell / originating
//! witness op); 2 = usage or I/O error.

use std::path::PathBuf;
use std::process::exit;

fn usage() -> ! {
    eprintln!("usage: witgen-interp check --export-dir DIR [--chip NAME] [--verbose]");
    exit(2);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut it = args.iter();
    if it.next().map(String::as_str) != Some("check") {
        usage();
    }
    let mut export_dir: Option<PathBuf> = None;
    let mut chip: Option<String> = None;
    let mut verbose = false;
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--export-dir" => {
                export_dir = Some(PathBuf::from(it.next().unwrap_or_else(|| usage())))
            }
            "--chip" => chip = Some(it.next().unwrap_or_else(|| usage()).clone()),
            "--verbose" => verbose = true,
            _ => usage(),
        }
    }
    let export_dir = export_dir.unwrap_or_else(|| {
        std::env::var("WITGEN_EXPORT_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|_| usage())
    });
    match witgen_interp::run_all(&export_dir, chip.as_deref(), verbose) {
        Ok((rows, failures)) if failures.is_empty() => {
            println!("witgen-interp: {rows} fixture rows reproduced exactly.");
        }
        Ok((rows, failures)) => {
            for f in &failures {
                eprintln!("FAIL: {f}");
            }
            eprintln!(
                "witgen-interp: {} mismatches across {rows} rows.",
                failures.len()
            );
            exit(1);
        }
        Err(e) => {
            eprintln!("witgen-interp: {e}");
            exit(2);
        }
    }
}
