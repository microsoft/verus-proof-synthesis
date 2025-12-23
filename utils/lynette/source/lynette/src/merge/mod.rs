use crate::deghost::*;
use crate::utils::*;
use crate::DeghostMode;
use quote::ToTokens;
use std::path::PathBuf;

mod exprs;
mod is_ghost;
mod merge;
mod types;
mod utils;

use merge::*;

/// Merge `filepath1` into `filepath2` with the given options.
///
/// Return the merged file as a `syn_verus::File`.
pub fn fmerge_files(
    filepath1: &PathBuf,
    filepath2: &PathBuf,
    mode: &DeghostMode,
) -> Result<syn_verus::File, Error> {
    fextract_verus_macro(filepath1).and_then(|(files1, orig)| {
        assert!(files1.len() == 1);
        fextract_verus_macro(filepath2)
            .and_then(|(files2, _)| {
                assert!(files2.len() == 1);

                let pure_rust_1 = remove_ghost_from_file(&files1[0], &DeghostMode::default());
                let pure_rust_2 = remove_ghost_from_file(&files2[0], &DeghostMode::default());
                assert!(pure_rust_1 == pure_rust_2);

                merge_files(&pure_rust_1, &files1[0], &files2[0], mode)
            })
            .and_then(|f| Ok(update_verus_macros_tss(&orig, vec![f.into_token_stream()])))
    })
}

// / Merge the functions specified in `funcs` in `filepath1` and `filepath2`
// / with the given options.
// /
// / The functions can only be exec-functions for now.
// /
// / The function performs a much less strict checking than `fmerge_files`.
// /
// / Return the merged file as a `syn_verus::File`.

// pub fn fmerge_funcs(
//     filepath1: &PathBuf,
//     filepath2: &PathBuf,
//     funcs: &Vec<String>,
//     mode: &DeghostMode,
// ) -> Result<syn_verus::File, Error> {
//     fextract_verus_macro(filepath1).and_then(|(files1, orig)| {
//         assert!(files1.len() == 1);
//         fextract_verus_macro(filepath2)
//             .and_then(|(files2, _)| {
//                 assert!(files2.len() == 1);

//                 funcs.iter().map(|fname| {
//                     extract_functions_by_name(&files1[0], fname)
//                         .and_then(|(f1, _)| extract_functions_by_name(&files2[0], fname).map(|(f2, _)| (f1, f2)))
//                 })

//                 let pure_rust_1 = remove_ghost_from_file(&files1[0], &DeghostMode::default());
//                 let pure_rust_2 = remove_ghost_from_file(&files2[0], &DeghostMode::default());
//                 assert!(pure_rust_1 == pure_rust_2);

//                 merge_files(&pure_rust_1, &files1[0], &files2[0], mode)
//             })
//             .and_then(|f| Ok(update_verus_macros_tss(&orig, vec![f.into_token_stream()])))
//     })
// }
