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
    eprintln!("       witgen-interp bench --export-dir DIR --chip NAME [--iters N]");
    eprintln!("       witgen-interp check-ensemble --instance FILE --trace FILE");
    exit(2);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut it = args.iter();
    let mode = it.next().map(|s| s.to_string());
    let mode = mode.as_deref();
    if mode == Some("check-ensemble") {
        let mut instance = None;
        let mut trace = None;
        while let Some(arg) = it.next() {
            match arg.as_str() {
                "--instance" if instance.is_none() => instance = it.next().map(PathBuf::from),
                "--trace" if trace.is_none() => trace = it.next().map(PathBuf::from),
                _ => usage(),
            }
        }
        let instance = instance.unwrap_or_else(|| usage());
        let trace = trace.unwrap_or_else(|| usage());
        let read_json = |path: &PathBuf| -> Result<serde_json::Value, String> {
            let bytes = std::fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
            serde_json::from_slice(&bytes).map_err(|error| format!("{}: {error}", path.display()))
        };
        let checked = (|| -> Result<(), String> {
            let instance = witgen_interp::ensemble_wire::parse_instance(&read_json(&instance)?)?;
            let trace = witgen_interp::ensemble_wire::parse_trace(&read_json(&trace)?)?;
            instance.check_trace::<witgen_interp::field::KoalaBear>(&trace)
        })();
        match checked {
            Ok(()) => println!("witgen-interp: native ensemble constraints and channel balance hold."),
            Err(error) => {
                eprintln!("witgen-interp: {error}");
                exit(1);
            }
        }
        return;
    }
    if mode != Some("check") && mode != Some("bench") {
        usage();
    }
    let mut export_dir: Option<PathBuf> = None;
    let mut chip: Option<String> = None;
    let mut verbose = false;
    let mut iters = 10_000usize;
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--export-dir" => {
                export_dir = Some(PathBuf::from(it.next().unwrap_or_else(|| usage())))
            }
            "--chip" => chip = Some(it.next().unwrap_or_else(|| usage()).clone()),
            "--verbose" => verbose = true,
            "--iters" => {
                iters = it
                    .next()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or_else(|| usage())
            }
            _ => usage(),
        }
    }
    let export_dir = export_dir.unwrap_or_else(|| {
        std::env::var("WITGEN_EXPORT_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|_| usage())
    });
    if mode == Some("bench") {
        let chip = chip.unwrap_or_else(|| usage());
        match witgen_interp::bench(&export_dir, &chip, iters) {
            Ok(rps) => {
                println!("{chip}: {rps:.0} rows/s ({iters} iterations, witgen + full row)");
                return;
            }
            Err(e) => {
                eprintln!("witgen-interp: {e}");
                exit(2);
            }
        }
    }
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
