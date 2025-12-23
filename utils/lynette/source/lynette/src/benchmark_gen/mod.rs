use std::path::PathBuf;
use std::process::Command;
use std::fs;
use std::io::Write;
use prettyplease_verus;
use crate::{utils::*};

mod benchmark_utils;
mod reorder;
mod erase_ghost;
mod remove_helper_lemma;
mod clean_uses;

use reorder::*;
use erase_ghost::*;
use remove_helper_lemma::*;
use clean_uses::*;

pub fn benchmark_cleanup(file: PathBuf, cleaned_file: PathBuf, no_lemma_mode: bool) -> Result<(), Error> {
    eprintln!("Loading file...");

    let mut new_file = fload_file(&file)?;

    eprintln!("Ordering...");
    order_target_item_last(&mut new_file);

    eprintln!("Erasing ghost...");
    // remove ghost from target fn
    erase_ghost_from_target(&mut new_file);

    eprintln!("Cleaning uses...");
    clean_uses(&mut new_file);

    if no_lemma_mode {
        eprintln!("Removing helper lemmas...");
        // erase all other lemmas
        remove_helper_lemma(&mut new_file);
    }

    // first use prettyplease, then run verusfmt
    let formatted = prettyplease_verus::unparse(&new_file);
    fs::write(cleaned_file.clone(), formatted).and_then(|_| {
        let mut cmd = Command::new("verusfmt");

        cmd.arg(cleaned_file.clone());

        cmd.status().expect("failed to execute verusfmt");
        Ok(())
    }).or_else(|e| {
        Err(Error::WriteFile(e))
    })
}

#[cfg(test)]
mod benchmark_tests {
    use super::*;

    const REORDER_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\reorder_lemma.rs";
    const REORDER_LEMMA_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\reorder_lemma_result.rs";
    const REORDER_IMPL: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\reorder_impl.rs";
    const REORDER_IMPL_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\reorder_impl_result.rs";
    const REORDER_TRAIT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\reorder_trait.rs";
    const REORDER_TRAIT_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\reorder_trait_result.rs";

    const ERASE_GHOST_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_lemma.rs";
    const ERASE_GHOST_LEMMA_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_lemma_result.rs";
    const ERASE_GHOST_LEMMA_RETURN: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_lemma_return.rs";
    const ERASE_GHOST_LEMMA_RETURN_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_lemma_return_result.rs";
    const ERASE_GHOST_IMPL: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_impl.rs";
    const ERASE_GHOST_IMPL_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_impl_result.rs";
    const ERASE_GHOST_TRAIT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_trait.rs";
    const ERASE_GHOST_TRAIT_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_ghost_trait_result.rs";
    const ERASE_ATTRS: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_attrs.rs";
    const ERASE_ATTRS_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\erase_attrs_result.rs";

    const REMOVE_HELPER_LEMMA: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\remove_helper_lemma.rs";
    const REMOVE_HELPER_LEMMA_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\remove_helper_lemma_result.rs";
    const REMOVE_HELPER_IMPL: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\remove_helper_impl.rs";
    const REMOVE_HELPER_IMPL_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\remove_helper_impl_result.rs";
    const REMOVE_HELPER_TRAIT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\remove_helper_trait.rs";
    const REMOVE_HELPER_TRAIT_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\remove_helper_trait_result.rs";

    const CLEAN_USES: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\clean_uses.rs";
    const CLEAN_USES_RESULT: &str = "C:\\Users\\t-nneamtu\\source\\Verus_Copilot\\utils\\lynette\\testcases_benchmark_gen\\clean_uses_result.rs";

    fn compare_results(orig: PathBuf, expected: PathBuf, no_lemma_mode: bool) -> Result<(), Error> {
        let mut tmp_file = tempfile::NamedTempFile::new().expect("Failed to create temp file");

        tmp_file.flush().expect("Failed to flush temp file");

        let tmp_path = tmp_file.path().to_owned();
        tmp_file.close().expect("Failed to close temp file");

        benchmark_cleanup(orig, tmp_path.clone(), no_lemma_mode)?;
        fs::read_to_string(tmp_path).and_then(|tmp_contents| {
            fs::read_to_string(expected).and_then(|expected_contents| {
                assert_eq!(tmp_contents, expected_contents);
                Ok(())
            })
        }).or_else(|e| {
            Err(Error::ReadFile(e))
        })
    }

    #[test]
    fn test_reorder_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(REORDER_LEMMA);
        let changed = PathBuf::from(REORDER_LEMMA_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn test_reorder_impl() -> Result<(), Error> {
        let orig = PathBuf::from(REORDER_IMPL);
        let changed = PathBuf::from(REORDER_IMPL_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn test_reorder_trait() -> Result<(), Error> {
        let orig = PathBuf::from(REORDER_TRAIT);
        let changed = PathBuf::from(REORDER_TRAIT_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn erase_ghost_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(ERASE_GHOST_LEMMA);
        let changed = PathBuf::from(ERASE_GHOST_LEMMA_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn erase_ghost_lemma_return() -> Result<(), Error> {
        let orig = PathBuf::from(ERASE_GHOST_LEMMA_RETURN);
        let changed = PathBuf::from(ERASE_GHOST_LEMMA_RETURN_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn erase_ghost_impl() -> Result<(), Error> {
        let orig = PathBuf::from(ERASE_GHOST_IMPL);
        let changed = PathBuf::from(ERASE_GHOST_IMPL_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn erase_ghost_trait() -> Result<(), Error> {
        let orig = PathBuf::from(ERASE_GHOST_TRAIT);
        let changed = PathBuf::from(ERASE_GHOST_TRAIT_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn erase_attrs() -> Result<(), Error> {
        let orig = PathBuf::from(ERASE_ATTRS);
        let changed = PathBuf::from(ERASE_ATTRS_RESULT);
        compare_results(orig, changed, false)
    }

    #[test]
    fn remove_helper_lemma() -> Result<(), Error> {
        let orig = PathBuf::from(REMOVE_HELPER_LEMMA);
        let changed = PathBuf::from(REMOVE_HELPER_LEMMA_RESULT);
        compare_results(orig, changed, true)
    }

    #[test]
    fn remove_helper_impl() -> Result<(), Error> {
        let orig = PathBuf::from(REMOVE_HELPER_IMPL);
        let changed = PathBuf::from(REMOVE_HELPER_IMPL_RESULT);
        compare_results(orig, changed, true)
    }

    #[test]
    fn remove_helper_trait() -> Result<(), Error> {
        let orig = PathBuf::from(REMOVE_HELPER_TRAIT);
        let changed = PathBuf::from(REMOVE_HELPER_TRAIT_RESULT);
        compare_results(orig, changed, true)
    }

    #[test]
    fn clean_uses_trait() -> Result<(), Error> {
        let orig = PathBuf::from(CLEAN_USES);
        let changed = PathBuf::from(CLEAN_USES_RESULT);
        compare_results(orig, changed, false)
    }
}
