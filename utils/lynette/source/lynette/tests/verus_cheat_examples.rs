use std::path::{Path, PathBuf};
use std::fs;
use std::panic;
use gag::Gag;
use lynette::check_allowed_additions_only;

/// Returns the path to the testcases directory relative to the project root
fn testcases_dir() -> PathBuf {
    // The test runs from the project root, so we navigate to testcases
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("testcases")
        .join("verus-cheat-examples")
}

/// Discovers all test cases in a directory.
/// Returns pairs of (input_file, changed_file, expected_result).
///
/// Convention:
/// - `fix-v0-input.rs` is the original file
/// - `fix-*.rs` (other than v0) are the changed files to test against
fn discover_test_cases(dir: &Path) -> Vec<(PathBuf, PathBuf)> {
    let mut test_cases = Vec::new();

    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_dir() {
                let input_file = path.join("fix-v0-input.rs");
                if input_file.exists() {
                    // Find all fix-*.rs files except fix-v0-input.rs
                    if let Ok(files) = fs::read_dir(&path) {
                        for file in files.filter_map(|f| f.ok()) {
                            let file_path = file.path();
                            let file_name = file_path.file_name()
                                .and_then(|n| n.to_str())
                                .unwrap_or("");

                            if file_name.starts_with("fix-")
                                && file_name.ends_with(".rs")
                                && file_name != "fix-v0-input.rs"
                            {
                                test_cases.push((input_file.clone(), file_path));
                            }
                        }
                    }
                }
            }
        }
    }

    // Sort for deterministic ordering
    test_cases.sort();
    test_cases
}

#[test]
fn test_verus_cheat_examples() {
    let test_dir = testcases_dir();

    if !test_dir.exists() {
        return;
    }

    let test_cases = discover_test_cases(&test_dir);

    // Group by directory for clearer output
    let mut by_dir: std::collections::HashMap<String, Vec<(PathBuf, PathBuf)>> =
        std::collections::HashMap::new();

    for (input, changed) in test_cases {
        let dir_name = input.parent()
            .and_then(|p| p.file_name())
            .and_then(|n| n.to_str())
            .unwrap_or("unknown")
            .to_string();
        by_dir.entry(dir_name).or_default().push((input, changed));
    }

    for (dir_name, cases) in by_dir.iter() {
        println!("\n=== {} ({} test cases) ===", dir_name, cases.len());

        for (input_file, changed_file) in cases {
            let file_name = changed_file.file_name().unwrap().to_str().unwrap();

            let input = input_file.clone();
            let changed = changed_file.clone();

            // Suppress stdout and stderr from the library during execution
            let result = {
                let _stdout_gag = Gag::stdout().ok();
                let _stderr_gag = Gag::stderr().ok();
                panic::catch_unwind(|| {
                    check_allowed_additions_only(input, changed)
                })
            };

            match result {
                Ok(Ok(true)) => println!("  [PASS] {}", file_name),
                Ok(Ok(false)) => println!("  [FAIL] {} - disallowed changes", file_name),
                Ok(Err(e)) => println!("  [ERR]  {} - {}", file_name, e),
                Err(_) => println!("  [PANIC] {}", file_name),
            }
        }
    }
}
